import Erdos64EG.CT12TypeBOverlapSupport
import StructuralExhaustion.Core.FiniteResolution

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact resolution split for every high center in a Type B scope

Unlike a caller-supplied assigned-center list, `TypeBSupportScope` supplies
only a literal vertex support and ordinary reserve.  Its demand centers are
derived as all ambient-degree-at-least-four vertices in that support.  The
common finite-resolution theorem then proves the exhaustive split:

* one actual high center has no certificate-closed or verified positive-B1
  local entry; or
* every actual high center has such an entry, yielding the concrete dependent
  CT12 family and therefore a full disjoint choice or a minimal obstruction.

No local entry, completeness assertion, or residual predicate is supplied as
a field of the scope.
-/

structure TypeBSupportScope
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  vertices : Finset ctx.G.Vertex
  /-- Finite external/decorative incidence assignment used in addition to all
  induced core incidences. -/
  assignedCarriers : Finset (Graph.FanClosedPort.LocalCarrier ctx.G.Vertex)
  reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- The counted Type B core is always a literal subset of the verified
`P₁₃` remainder, regardless of the caller's proposed scope set. -/
noncomputable def coreVertices : Finset ctx.G.Vertex := by
  classical
  exact scope.vertices ∩ p13RemainderVertices ctx

theorem coreVertices_subset_remainder :
    scope.coreVertices ⊆ p13RemainderVertices ctx := by
  classical
  exact Finset.inter_subset_right

theorem coreVertices_subset_vertices :
    scope.coreVertices ⊆ scope.vertices := by
  classical
  exact Finset.inter_subset_left

noncomputable def highCenters : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact scope.coreVertices.filter fun center => 4 ≤ ctx.G.object.degree center

abbrev Center := {center : ctx.G.Vertex // center ∈ scope.highCenters}

@[implicit_reducible]
noncomputable def centers : FinEnum scope.Center := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Core.Enumeration.subtype ctx.G.object.input.vertices
    (fun center => center ∈ scope.highCenters) (fun _center => inferInstance)

theorem center_mem_vertices (center : scope.Center) :
    center.1 ∈ scope.vertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact scope.coreVertices_subset_vertices (Finset.mem_filter.mp member).1

theorem center_mem_coreVertices (center : scope.Center) :
    center.1 ∈ scope.coreVertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact (Finset.mem_filter.mp member).1

theorem center_high (center : scope.Center) :
    4 ≤ ctx.G.object.degree center.1 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact (Finset.mem_filter.mp member).2

/-- Actual assigned incidences: every induced core edge plus the finite
external/decorative assignment, always intersected with graph adjacency. -/
def Assigned (carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex) : Prop :=
  ctx.G.object.graph.Adj carrier.1 carrier.2 ∧
    (carrier ∈ scope.assignedCarriers ∨
      (carrier.1 ∈ scope.coreVertices ∧ carrier.2 ∈ scope.coreVertices))

noncomputable def assignedDecidable : ∀ carrier, Decidable (scope.Assigned carrier) := by
  intro carrier
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  unfold Assigned
  exact inferInstance

/-- Exact local-entry proposition at one derived center. -/
def LocalEntryAt (center : scope.Center) :=
  {entry : TypeBLocalEntry ctx //
    entry.center = center.1 ∧
      (∀ carrier, entry.Assigned carrier ↔ scope.Assigned carrier) ∧
        entry.CoreCompatible scope.coreVertices}

noncomputable def resolutionProfile : Core.FiniteResolution.Profile scope.Center where
  Witness := scope.LocalEntryAt
  sites := scope.centers

abbrev FullResolution := scope.resolutionProfile.FullResolution

/-- The negative branch is literally absence of either already verified
local fan entry at an actual high center. -/
def UnresolvedCenter : Prop :=
  ∃ center : scope.Center, ¬Nonempty (scope.LocalEntryAt center)

/-- A full local resolution canonically creates the assigned Type B support;
the center set is not chosen independently. -/
noncomputable def assignedSupport (resolution : scope.FullResolution) :
    TypeBAssignedSupport ctx where
  vertices := scope.coreVertices
  vertices_remainder := scope.coreVertices_subset_remainder
  assignedCarriers := scope.assignedCarriers
  centers := scope.highCenters
  centers_exact := rfl
  entry := fun center => (resolution.witness center).1
  entry_center := fun center => (resolution.witness center).2.1
  entry_assigned := fun center carrier => (resolution.witness center).2.2.1 carrier
  entry_coreCompatible := fun center => (resolution.witness center).2.2.2
  baseReserve := scope.reserve

/-- Fully stratified Type B alternative on the entire derived high-center
set of the scope. -/
theorem unresolved_or_fullChoice_or_minimalOverlap :
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let assigned := scope.assignedSupport resolution
        Nonempty assigned.completionProfile.FullChoice ∨
          Nonempty assigned.MinimalOverlap := by
  rcases scope.resolutionProfile.fullResolution_or_unresolved with
    resolved | unresolved
  · right
    let resolution := Classical.choice resolved
    refine ⟨resolution, ?_⟩
    let assigned := scope.assignedSupport resolution
    rcases assigned.full_choice_or_minimal_obstruction with choice | obstruction
    · exact Or.inl choice
    · exact Or.inr ⟨⟨obstruction.choose, obstruction.choose_spec.1,
          obstruction.choose_spec.2⟩⟩
  · left
    exact unresolved

end TypeBSupportScope

/-- Verified endpoint for the graph-derived high-center schedule and its
complete local-resolution/choice/obstruction state-space split. -/
structure VerifiedTypeBResolutionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTypeBOverlapSupportPrefix ctx
  total : ∀ scope : TypeBSupportScope ctx,
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let assigned := scope.assignedSupport resolution
        Nonempty assigned.completionProfile.FullChoice ∨
          Nonempty assigned.MinimalOverlap

noncomputable def verifiedTypeBResolutionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBOverlapSupportPrefix ctx) :
    VerifiedTypeBResolutionPrefix ctx where
  previous := previous
  total := fun scope => scope.unresolved_or_fullChoice_or_minimalOverlap

theorem exists_verifiedTypeBResolutionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBResolutionPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTypeBOverlapSupportPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBResolutionPrefix ctx previous⟩

end Erdos64EG.Internal
