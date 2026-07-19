import StructuralExhaustion.Core.ListPosition
import StructuralExhaustion.CT6.Automation
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Graph.ChordCycle
import StructuralExhaustion.Graph.MaximalPath
import StructuralExhaustion.Graph.MinimumDegreeCycle
import StructuralExhaustion.Routes.CT6ToCT9

namespace StructuralExhaustion.Graph.EndpointParityCycle

open StructuralExhaustion

universe u

/-!
# Endpoint-parity cycle profile

This module owns the reusable greedy-path/CT6/CT9 proof pattern.  An
application starts with the existing `MinimumDegreeCycle.StaticInput`, proves
that its threshold is at least three, and explains how an even cycle satisfies
its selected length predicate.  The framework then generates the exact path,
both tactic runs, their typed route, the same-parity endpoint chords, and the
target certificate.
-/

/-- Dependent branch state of the endpoint-extension machine. -/
abbrev PathState {V : Type u} (object : FiniteObject V) :=
  (root : V) × RootedPath object.graph root

/-- Static contract for the endpoint-parity proof pattern. -/
structure Profile (V : Type u) where
  base : MinimumDegreeCycle.StaticInput.{u, u} V PathState
  three_le_minimumDegree : 3 ≤ base.minimumDegree
  acceptsEven : ∀ length, length % 2 = 0 → base.LengthOK length

/-- Same-parity endpoint-neighbour positions carried by a CT9 collision. -/
structure SameParityEndpointPositions {V : Type u}
    {object : FiniteObject V} {root : V}
    (path : RootedPath object.graph root) where
  left : Nat
  right : Nat
  left_mem : left ∈
    @RootedPath.endpointNeighborPositions V object.graph root
      object.input.decideAdj path
  right_mem : right ∈
    @RootedPath.endpointNeighborPositions V object.graph root
      object.input.decideAdj path
  distinct : left ≠ right
  same_parity : left % 2 = right % 2

namespace Profile

variable {V : Type u}

/-- Canonical minimum-degree-three/even-cycle profile. -/
@[reducible]
def evenCycle (V : Type u) : Profile V where
  base := {
    minimumDegree := 3
    LengthOK := fun length => length % 2 = 0
  }
  three_le_minimumDegree := le_rfl
  acceptsEven := fun _length even => even

private theorem vertexOrder_nonempty (profile : Profile V)
    (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    object.input.vertices.orderedValues ≠ [] := by
  have three : 3 ≤ object.minDegree :=
    profile.three_le_minimumDegree.trans baseline
  obtain ⟨vertex⟩ := object.nonempty_of_minDegree_pos (by omega)
  intro empty
  have member := object.input.vertices.mem_orderedValues vertex
  simp [empty] at member

/-- Deterministic greedy endpoint-maximal path with its root retained. -/
def chosenMaximalPath (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    Σ root, EndpointMaximalPath object.graph root :=
  ⟨object.input.vertices.orderedValues.head
      (profile.vertexOrder_nonempty object baseline),
    endpointMaximalPath object.input
      (profile.vertexOrder_nonempty object baseline)⟩

/-- Active path of the generated branch state. -/
def activePath (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    RootedPath object.graph (profile.chosenMaximalPath object baseline).1 :=
  (profile.chosenMaximalPath object baseline).2.path

/-- Shared branch input inherited definitionally by CT9. -/
def branchContext (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    Core.BranchContext profile.base.problem where
  G := object
  baseline := baseline
  state := ⟨(profile.chosenMaximalPath object baseline).1,
    profile.activePath object baseline⟩

/-- CT6 searches the vertex schedule for a fresh endpoint neighbour. -/
def ct6Spec (profile : Profile V) : CT6.Spec profile.base.problem where
  Index := V
  FailureData := V
  Failure := fun context vertex =>
    CanExtend context.G.graph context.state.2 vertex
  failureData := fun _context vertex _failure => vertex
  contribution := fun context vertex =>
    @ite Nat (context.G.graph.Adj context.state.2.endpoint vertex)
      (context.G.input.decideAdj _ _) 1 0

/-- Exact CT6 search capability in the declared vertex order. -/
def ct6Capability (profile : Profile V) (object : FiniteObject V) :
    CT6.Capability profile.ct6Spec where
  failureOrder := object.input.vertices
  failureDecidable := fun context vertex =>
    canExtendDecidable context.G.input context.state.2 vertex

theorem ct6_no_failure (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) (vertex : V) :
    ¬ profile.ct6Spec.Failure (profile.branchContext object baseline) vertex := by
  intro failure
  apply (profile.chosenMaximalPath object baseline).2.no_fresh_endpoint_neighbor
    vertex
  have unpacked :
      object.graph.Adj vertex (profile.activePath object baseline).endpoint ∧
        vertex ∉ (profile.activePath object baseline).vertices := by
    simpa [ct6Spec, branchContext, CanExtend, activePath] using failure
  exact ⟨unpacked.1.symm, unpacked.2⟩

/-- Exact active-ledger CT6 execution. -/
def ct6Run (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT6.ActiveLedgerRun profile.ct6Spec (profile.ct6Capability object)
      (profile.branchContext object baseline) :=
  CT6.runActiveLedgerOfNoFailure profile.ct6Spec
    (profile.ct6Capability object) (profile.branchContext object baseline)
    (profile.ct6_no_failure object baseline)

/-- Endpoint closure extracted from the actual CT6 residual. -/
theorem ct6_endpoint_closed (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    ∀ vertex,
      object.graph.Adj (profile.activePath object baseline).endpoint vertex →
      vertex ∈ (profile.activePath object baseline).vertices := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex adjacent
  have noFailure := (profile.ct6Run object baseline).residual.noFailure vertex
  by_cases member : vertex ∈ (profile.activePath object baseline).vertices
  · exact member
  · exact (noFailure ⟨adjacent.symm, member⟩).elim

/-! ## CT9 parity overload and routed position certificate -/

/-- Canonical position rank on the active path. -/
def endpointRank (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) (vertex : V) : Nat := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (profile.activePath object baseline).vertices.idxOf vertex

def ct9ParityProfile (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT9.ParityCapacityOneSpec profile.base.problem where
  Item := V
  rank := profile.endpointRank object baseline

abbrev ct9Capability (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :=
  (profile.ct9ParityProfile object baseline).capability

/-- Endpoint neighbours in the same explicit order used by CT6. -/
def endpointNeighborItems (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    Core.OrderedCollection V :=
  object.input.orderedNeighbors (profile.activePath object baseline).endpoint

def ct6ToCT9ItemAdapter (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    Routes.CT6ToCT9.ItemCollectionAdapter
      (CT6.ActiveLedgerResidual profile.ct6Spec
        (profile.ct6Capability object) (profile.branchContext object baseline))
      (profile.ct9Capability object baseline).Item :=
  Routes.CT6ToCT9.ItemCollectionAdapter.constant
    (profile.endpointNeighborItems object baseline)

/-- Exact CT6 residual stage consumed by the framework transition. -/
def ct6SourceStage (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :=
  Core.Routing.ResidualStage.exact (tactic := .ct6)
    (profile.ct6Run object baseline)

/-- Framework-owned CT6→CT9 transition instantiated by this graph profile. -/
abbrev ct6ToCT9Transition (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :=
  Routes.CT6ToCT9.transition (profile.ct9Capability object baseline)
    (profile.ct6ToCT9ItemAdapter object baseline)

/-- Enabled CT9 execution retaining the complete incoming CT6 stage. -/
def ct6ToCT9Stage (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :=
  Routes.CT6ToCT9.advance (profile.ct9Capability object baseline)
    (profile.ct6ToCT9ItemAdapter object baseline)
    (fun ledger => ledger.residual)
    (profile.ct6SourceStage object baseline)

/-- Accumulated CT9 ledger used by every downstream transition. -/
def ct6ToCT9Ledger (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :=
  profile.ct6ToCT9Stage object baseline

/-- CT9 input read from the executable transition; no graph module rebuilds
the route context or trigger. -/
def ct9Input (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT9.Input (profile.ct9Capability object baseline) :=
  let transition := profile.ct6ToCT9Transition object baseline
  let execution := transition.onLedger (fun ledger => ledger.residual)
  let source := profile.ct6SourceStage object baseline
  CT9.Input.ofTrigger (execution.targetContext source)
    (execution.trigger source ())

theorem ct9_three_le_item_cardinality (profile : Profile V)
    (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    3 ≤ (profile.ct9Input object baseline).items.values.length := by
  change 3 ≤ (object.input.orderedNeighbors
    (profile.activePath object baseline).endpoint).values.length
  rw [FiniteInput.orderedNeighbors_length]
  exact (profile.three_le_minimumDegree.trans baseline).trans
    (object.minDegree_le_degree (profile.activePath object baseline).endpoint)

/-- Exact CT9 overload execution. -/
def ct9Run (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT9.ParityCapacityOneRun (profile.endpointRank object baseline)
      (profile.ct9Input object baseline) :=
  CT9.runParityCapacityOneOfThreeLeCardinality
    (profile.endpointRank object baseline) (profile.ct9Input object baseline)
    (profile.ct9_three_le_item_cardinality object baseline)

/-- Generic conversion from CT9's same-label vertex collision to positions on
the active rooted path. -/
def sameParityEndpointPositions (profile : Profile V)
    (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    SameParityEndpointPositions (profile.activePath object baseline) := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let path := profile.activePath object baseline
  let pair := (profile.ct9Run object baseline).pair
  have firstEdge : object.graph.Adj path.endpoint pair.first :=
    (object.input.mem_orderedNeighbors_iff path.endpoint pair.first).mp
      pair.first_mem
  have secondEdge : object.graph.Adj path.endpoint pair.second :=
    (object.input.mem_orderedNeighbors_iff path.endpoint pair.second).mp
      pair.second_mem
  have firstPathMem : pair.first ∈ path.vertices :=
    profile.ct6_endpoint_closed object baseline pair.first firstEdge
  have secondPathMem : pair.second ∈ path.vertices :=
    profile.ct6_endpoint_closed object baseline pair.second secondEdge
  let located := Core.ListPosition.locateDistinctPair
    firstPathMem secondPathMem pair.distinct
  have leftPosition : located.left ∈ path.endpointNeighborPositions :=
    (path.mem_endpointNeighborPositions_iff located.left).mpr
      ⟨located.left_lt, by simpa [located.left_value] using firstEdge⟩
  have rightPosition : located.right ∈ path.endpointNeighborPositions :=
    (path.mem_endpointNeighborPositions_iff located.right).mpr
      ⟨located.right_lt, by simpa [located.right_value] using secondEdge⟩
  exact {
    left := located.left
    right := located.right
    left_mem := leftPosition
    right_mem := rightPosition
    distinct := located.positions_distinct
    same_parity := by
      simpa [endpointRank, activePath, path, located.left_eq,
        located.right_eq] using pair.same_parity
  }

/-! ## Chord-cycle and target certificates -/

/-- Even cycle extracted from the routed CT9 collision. -/
def evenCycleCertificate (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CycleWithLength object.graph (fun length => length % 2 = 0) := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let path := profile.activePath object baseline
  let pair := profile.sameParityEndpointPositions object baseline
  by_cases ordered : pair.left < pair.right
  · exact path.evenCycleOfEndpointNeighborPositions pair.left_mem
      pair.right_mem ordered pair.same_parity
  · have reverse : pair.right < pair.left :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) pair.distinct.symm
    exact path.evenCycleOfEndpointNeighborPositions pair.right_mem
      pair.left_mem reverse pair.same_parity.symm

/-- Convert the even cycle to the profile's selected length target. -/
def targetCertificate (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CycleWithLength object.graph profile.base.LengthOK := by
  let even := profile.evenCycleCertificate object baseline
  exact {
    vertex := even.vertex
    walk := even.walk
    isCycle := even.isCycle
    length_ok := profile.acceptsEven even.walk.length even.length_ok
  }

/-- Public target theorem generated by the complete endpoint-parity profile. -/
theorem target_of_baseline (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    profile.base.Target object :=
  ⟨profile.targetCertificate object baseline⟩

/-! ## CT1 validation of the generated target -/

/-- Canonical CT1 input retaining the same branch context used by CT6 and
CT9. -/
def ct1Input (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT1.Input profile.base.problem where
  context := profile.branchContext object baseline

/-- Exact successful CT1 execution for the target certificate generated by
the endpoint-parity profile. -/
def ct1Run (profile : Profile V) (object : FiniteObject V)
    (baseline : profile.base.problem.Baseline object) :
    CT1.CertifiedC1Run profile.base.ct1Spec
      (profile.ct1Input object baseline) :=
  profile.base.targetEncoding.run (profile.ct1Input object baseline)
    (profile.targetCertificate object baseline) trivial

end Profile

end StructuralExhaustion.Graph.EndpointParityCycle
