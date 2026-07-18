import StructuralExhaustion.Graph.SurplusPatternCoarseRouting

namespace StructuralExhaustion.Graph.SurplusPatternRoutingObservations

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)

open SurplusPatternCoarseRouting

/-!
# Literal fields of the same-token routing label

These definitions extract only fields already determined by one routed pair.
They neither enumerate the ambient window family nor assert a uniform bound on
the resulting full routing-label type.
-/

/-- Degree of one port vertex inside the manuscript's bounded support `T(p)`.
This is deliberately not its ambient degree in `G`. -/
def portSupportDegree (pair : Pair (setup := setup)) (first : Bool)
    (role : SurplusPortActivation.PortRole) : Nat := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  exact (ctx.G.object.graph.neighborFinset
    (SurplusPortActivation.portVertex setup (pairSlot pair first) role) ∩
      SurplusPortActivation.PortSupport setup (pairSlot pair first)).card

theorem portSupportDegree_le_three (pair : Pair (setup := setup))
    (first : Bool) (role : SurplusPortActivation.PortRole) :
    portSupportDegree (ctx := ctx) pair first role ≤ 3 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  calc
    portSupportDegree (ctx := ctx) pair first role ≤
        (SurplusPortActivation.PortSupport setup
          (pairSlot pair first)).card := by
      exact Finset.card_le_card Finset.inter_subset_right
    _ = 3 := SurplusPortActivation.portSupport_card setup (pairSlot pair first)

/-- The six boundary-degree entries of the two bounded three-vertex port
supports.  The range `Fin 4` gives the graph-independent finite coordinate
required by the paper's `Q_geom` routing label. -/
noncomputable def boundaryDegreeProfile (pair : Pair (setup := setup)) :
    Bool → SurplusPortActivation.PortRole → Fin 4 :=
  fun first role =>
    ⟨portSupportDegree (ctx := ctx) pair first role,
      by have := portSupportDegree_le_three (ctx := ctx) pair first role; omega⟩

/-- Exact graph-independent universe containing every six-entry bounded
support degree profile. Impossible entries may occur in the universe, but the
encoding of an actual profile is lossless. -/
@[implicit_reducible]
def boundedDegreeProfiles :
    FinEnum (Bool → SurplusPortActivation.PortRole → Fin 4) := by
  letI : FinEnum Bool := Core.Enumeration.bool
  letI : FinEnum SurplusPortActivation.PortRole :=
    FinEnum.ofList SurplusPortActivation.portRoles
      SurplusPortActivation.mem_portRoles
  exact inferInstance

@[simp] theorem boundedDegreeProfiles_card :
    boundedDegreeProfiles.card = 4096 := by
  native_decide

theorem boundaryDegreeProfile_apply
    (pair : Pair (setup := setup)) (first : Bool)
    (role : SurplusPortActivation.PortRole) :
    (boundaryDegreeProfile (ctx := ctx) pair first role).val =
      portSupportDegree (ctx := ctx) pair first role :=
  rfl

/-- Equality of the extracted profile preserves every bounded-support degree
entry; the `Fin 4` encoding is exact, not a truncation. -/
theorem boundaryDegreeProfile_eq_iff
    (left right : Pair (setup := setup)) :
    boundaryDegreeProfile (ctx := ctx) left =
        boundaryDegreeProfile (ctx := ctx) right ↔
      ∀ first role,
        portSupportDegree (ctx := ctx) left first role =
          portSupportDegree (ctx := ctx) right first role := by
  constructor
  · intro equal first role
    exact congrArg Fin.val (congrFun (congrFun equal first) role)
  · intro equal
    funext first role
    apply Fin.ext
    exact equal first role

/-- For one supplied packed window and one supplied role, the exact P13 label
is the set of the thirteen positions adjacent to that literal port vertex.
Only this fixed thirteen-position row is inspected. -/
noncomputable def windowAttachmentLabel
    (pair : Pair (setup := setup))
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (first : Bool) (role : SurplusPortActivation.PortRole) :
    InducedPathAttachment.Label 13 := by
  classical
  exact Finset.univ.filter fun position =>
    windowPortAttached (ctx := ctx) (setup := setup)
      pair window position first role

@[simp] theorem mem_windowAttachmentLabel_iff
    (pair : Pair (setup := setup))
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (position : Fin 13) (first : Bool)
    (role : SurplusPortActivation.PortRole) :
    position ∈ windowAttachmentLabel (ctx := ctx) pair window first role ↔
      windowPortAttached (ctx := ctx) (setup := setup)
        pair window position first role := by
  classical
  simp [windowAttachmentLabel]

/-- Equality of the exact labels on a supplied window is precisely
coordinatewise equality of its thirteen literal adjacency predicates. -/
theorem windowAttachmentLabel_eq_iff
    (left right : Pair (setup := setup))
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (first : Bool) (role : SurplusPortActivation.PortRole) :
    windowAttachmentLabel (ctx := ctx) left window first role =
        windowAttachmentLabel (ctx := ctx) right window first role ↔
      ∀ position : Fin 13,
        (windowPortAttached (ctx := ctx) (setup := setup)
            left window position first role ↔
          windowPortAttached (ctx := ctx) (setup := setup)
            right window position first role) := by
  classical
  constructor
  · intro equal position
    have membership := congrArg (fun label => position ∈ label) equal
    simpa using membership
  · intro equal
    ext position
    simpa using equal position

end StructuralExhaustion.Graph.SurplusPatternRoutingObservations
