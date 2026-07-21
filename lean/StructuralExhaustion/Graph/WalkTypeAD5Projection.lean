import StructuralExhaustion.Graph.WalkTypeASupportProfile
import StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate
import StructuralExhaustion.Graph.TypeAFirstEntryCoordinate
import StructuralExhaustion.Graph.TypeAReceiverEntryChannel
import StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate
import StructuralExhaustion.Graph.TypeBFanCenterCoordinate

namespace StructuralExhaustion.Graph.WalkTypeAD5Projection

open StructuralExhaustion

universe u

variable {V : Type u}

/-!
# Exact D5 base data on one proof-selected walk support

The degree split is local to the literal support.  A high vertex is returned
as the paper's D6 handoff.  If no high vertex exists, minimum degree three
makes the support ambient-cubic; properness and minimality then construct the
Type-A support profile.  The D5 schedule contains every canonical receiver
trace and every actual completion port, together with the canonical
bridgeless return, first entry, connector, connector length, and oriented
carrier incidence for that port.

Silent-basin and carrier-restriction quotients are not fabricated here: they
are generated only after the later saturated/route-8 classifier supplies the
corresponding routed loads.  This module constructs all D5 coordinates whose
declared support is already present on the walk interface.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {left right : ctx.G.Vertex}
variable (walk : ctx.G.object.graph.Walk left right)

noncomputable abbrev support : Finset ctx.G.Vertex :=
  WalkTypeASupportProfile.support ctx.G.object walk

noncomputable def highCenters : Finset ctx.G.Vertex :=
  NegativeSupportHandoff.highCentersAtLeast ctx.G.object 4 (support walk)

structure High where
  center : ctx.G.Vertex
  centerMem : center ∈ support walk
  centerHigh : 4 ≤ ctx.G.object.degree center
  d6Profile : TypeBFanCenterCoordinate.Profile ctx.G.object
  d6ProfileExact : d6Profile = { center := center, centerHigh := centerHigh }

structure NoHigh (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) where
  highCentersEmpty : highCenters walk = ∅
  ambientCubic : ∀ vertex ∈ support walk, ctx.G.object.degree vertex = 3

inductive DegreeResult (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) where
  | high (output : High walk)
  | noHigh (output : NoHigh walk minimumDegreeThree)

/-- One degree lookup per vertex of the supplied walk support. -/
noncomputable def degreeSplit (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) :
    DegreeResult walk minimumDegreeThree := by
  classical
  by_cases nonempty : (highCenters walk).Nonempty
  · let center := nonempty.choose
    have selected := Finset.mem_filter.mp nonempty.choose_spec
    let profile : TypeBFanCenterCoordinate.Profile ctx.G.object := {
      center := center
      centerHigh := selected.2
    }
    exact .high {
      center := center
      centerMem := selected.1
      centerHigh := selected.2
      d6Profile := profile
      d6ProfileExact := rfl
    }
  · have empty : highCenters walk = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    apply DegreeResult.noHigh
    refine { highCentersEmpty := empty, ambientCubic := ?_ }
    intro vertex member
    have lower : 3 ≤ ctx.G.object.degree vertex :=
      minimumDegreeThree.trans (ctx.G.object.minDegree_le_degree vertex)
    have notHigh : ¬4 ≤ ctx.G.object.degree vertex := by
      intro high
      have selected : vertex ∈ highCenters walk := by
        simpa [highCenters, NegativeSupportHandoff.highCentersAtLeast, member, high]
      rw [empty] at selected
      simp at selected
    omega

/-- Build the complete same-support Type-A ownership profile on the cubic
branch.  The outside vertex proves that this exact support is proper. -/
noncomputable def typeAProfile
    (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree)
    (minimumDegree_eq : input.minimumDegree = 3)
    (outside : ctx.G.Vertex) (outsideNotMem : outside ∉ support walk)
    (noHigh : NoHigh walk minimumDegreeThree) :
    TypeACanonicalReceiverTrace.SupportProfile ctx.G.object :=
  WalkTypeASupportProfile.profile ctx walk minimumDegree_eq noHigh.ambientCubic
    outside outsideNotMem

namespace Profile

variable (profile : TypeACanonicalReceiverTrace.SupportProfile ctx.G.object)

abbrev TraceCoordinate :=
  TypeATraceIncidenceCoordinate.Coordinate ctx.G.object profile

abbrev PortCoordinate :=
  TypeACompletionPortCoordinate.Coordinate ctx.G.object profile

/-- D5 labels already generated on the active interface: canonical trace
incidences and actual completion-port/connector coordinates. -/
abbrev Coordinate := TraceCoordinate profile ⊕ PortCoordinate profile

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate profile) := by
  letI : FinEnum (TraceCoordinate profile) :=
    TypeATraceIncidenceCoordinate.coordinates ctx.G.object profile
  letI : FinEnum (PortCoordinate profile) :=
    TypeACompletionPortCoordinate.coordinates ctx.G.object profile
  exact inferInstance

/-- CT2 bridgelessness, restricted to the already enumerated local ports. -/
abbrev ReturnProducer := TypeAAnchoredReturnCoordinate.Producer ctx.G.object profile

noncomputable def anchored (producer : ReturnProducer profile)
    (port : PortCoordinate profile) :=
  TypeAAnchoredReturnCoordinate.Producer.produce ctx.G.object profile producer port

noncomputable def firstEntry (producer : ReturnProducer profile)
    (port : PortCoordinate profile) :=
  TypeAFirstEntryCoordinate.select ctx.G.object profile port
    (anchored (ctx := ctx) profile producer port)

noncomputable def connector (producer : ReturnProducer profile)
    (port : PortCoordinate profile) :=
  TypeAReceiverEntryChannel.Connector.extract ctx.G.object profile port
    (anchored (ctx := ctx) profile producer port)
    (firstEntry (ctx := ctx) profile producer port)

/-- A uniform exact value record.  The label remains distinct from its value;
coincident numerical fields therefore never identify coordinates. -/
structure Value where
  declaredSupport : Finset ctx.G.Vertex
  primary : ctx.G.Vertex
  secondary : Option ctx.G.Vertex
  number : Nat
  flag : Bool

noncomputable def value (producer : ReturnProducer profile) :
    Coordinate profile → Value (ctx := ctx) (input := input)
  | .inl trace => {
      declaredSupport := trace.support ctx.G.object profile
      primary := trace.ambientVertex ctx.G.object profile
      secondary := none
      number := trace.internalDegree ctx.G.object profile
      flag := trace.terminal ctx.G.object profile
    }
  | .inr port => by
      let first := firstEntry (ctx := ctx) profile producer port
      let connector := connector (ctx := ctx) profile producer port
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      exact {
        declaredSupport := connector.path.support.toFinset ∪
          {(port.receiver ctx.G.object profile).1,
            port.outside ctx.G.object profile}
        primary := (port.receiver ctx.G.object profile).1
        secondary := some (first.entry ctx.G.object profile port
          (anchored (ctx := ctx) profile producer port))
        number := connector.length ctx.G.object profile port
          (anchored (ctx := ctx) profile producer port) first
        flag := true
      }

theorem coordinate_mem (coordinate : Coordinate profile) :
    coordinate ∈ (coordinates profile).orderedValues :=
  (coordinates profile).mem_orderedValues coordinate

theorem trace_support_subset (producer : ReturnProducer profile)
    (trace : TraceCoordinate profile) :
    (value profile producer (.inl trace)).declaredSupport ⊆ profile.support := by
  simpa [value] using
    trace.support_subset_profile ctx.G.object profile

noncomputable def visibleChecks : Nat :=
  TypeATraceIncidenceCoordinate.visibleChecks ctx.G.object profile +
    TypeACompletionPortCoordinate.visibleChecks ctx.G.object profile

theorem visibleChecks_polynomial :
    visibleChecks profile ≤
      ctx.G.object.input.vertices.card *
          (ctx.G.object.input.vertices.card + 1) +
        4 * ctx.G.object.input.vertices.card := by
  exact Nat.add_le_add
    (TypeATraceIncidenceCoordinate.visibleChecks_polynomial ctx.G.object profile)
    (TypeACompletionPortCoordinate.visibleChecks_polynomial ctx.G.object profile)

end Profile

end StructuralExhaustion.Graph.WalkTypeAD5Projection
