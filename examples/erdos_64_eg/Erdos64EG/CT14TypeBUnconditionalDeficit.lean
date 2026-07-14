import Erdos64EG.CT12TypeBResolution
import StructuralExhaustion.Graph.HighCenterDeletionCharge

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Unconditional Type B deficit bound

This stage bounds the charge of every literal Type B scope before any local
fan resolution or B2 carrier choice is made.  All actual high centers are
deleted.  The retained graph is a literal induced subgraph of the verified
`P₁₃` remainder, so the Hegde--Sandeep--Shashank theorem supplies its empty
internal three-core.  The reusable high-center deletion theorem then charges
the complete Type B deficit to actual assigned surplus and the exact receiver
overload of the retained Type A graph.

Consequently unresolved local entries and minimal B2 overlaps are genuine
state-space descriptions, but they are not loopholes in the quantitative
charge theorem.  No local candidate, disjointness assertion, or boundary
payment is assumed here.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

noncomputable def highCenterChargeProfile :
    Graph.AssignedSupportCharge.Profile ctx.G.object where
  core := scope.coreVertices
  assignedCenters := scope.highCenters

theorem highCenters_subset_coreVertices :
    scope.highCenters ⊆ scope.coreVertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  intro center member
  exact (Finset.mem_filter.mp member).1

theorem highCenter_member_degree
    {center : ctx.G.Vertex} (member : center ∈ scope.highCenters) :
    4 ≤ ctx.G.object.degree center := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (Finset.mem_filter.mp member).2

theorem nonHighCoreVertex_ambientDegree_eq_three
    {vertex : ctx.G.Vertex} (core : vertex ∈ scope.coreVertices)
    (notCenter : vertex ∉ scope.highCenters) :
    ctx.G.object.degree vertex = 3 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have notHigh : ¬4 ≤ ctx.G.object.degree vertex := by
    intro high
    exact notCenter (Finset.mem_filter.mpr ⟨core, high⟩)
  have lower : 3 ≤ ctx.G.object.degree vertex :=
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex)
  omega

noncomputable def highCenterDeletionProfile :
    Graph.HighCenterDeletionCharge.Profile ctx.G.object where
  charge := scope.highCenterChargeProfile
  centers_subset_core := scope.highCenters_subset_coreVertices
  center_high := fun _center member => scope.highCenter_member_degree member
  noncenter_degree_eq_three := fun _vertex core notCenter =>
    scope.nonHighCoreVertex_ambientDegree_eq_three core notCenter

/-- The choice-free profile is definitionally the same graph charge profile
used after any successful local resolution. -/
@[simp]
theorem assignedSupport_chargeProfile_eq
    (resolution : scope.FullResolution) :
    (scope.assignedSupport resolution).assignedChargeProfile =
      scope.highCenterChargeProfile := by
  rfl

theorem centerDeletedCore_subset_remainder :
    (scope.highCenterDeletionProfile).remainingCore ⊆
      p13RemainderVertices ctx := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  intro vertex member
  exact scope.coreVertices_subset_remainder (Finset.mem_sdiff.mp member).1

/-- Literal embedding of the center-deleted graph into the verified packed
path remainder. -/
noncomputable def centerDeletedToP13Embedding :
    (scope.highCenterDeletionProfile).remainingObject.graph ↪g
      (p13Remainder ctx).graph where
  toFun vertex :=
    ⟨vertex.1, scope.centerDeletedCore_subset_remainder vertex.2⟩
  inj' := by
    intro left right equal
    exact Subtype.ext
      (congrArg (fun vertex : P13RemainderVertex ctx => vertex.1) equal)
  map_rel_iff' := by
    intro left right
    rfl

theorem centerDeletedObject_p13Free :
    Graph.InducedPathFree
      (scope.highCenterDeletionProfile).remainingObject.graph 13 := by
  intro realization
  rcases realization with ⟨window⟩
  exact p13Remainder_free ctx
    ⟨(scope.centerDeletedToP13Embedding).comp window⟩

theorem centerDeletedObject_avoidsPowerOfTwoCycle :
    ¬Graph.HasCycleWithLength
      (scope.highCenterDeletionProfile).remainingObject.graph
      (fun length =>
        ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
  intro remainingCycle
  let embedding := ctx.G.object.induceFinsetEmbedding
    (scope.highCenterDeletionProfile).remainingCore
  have ambientCycle := Graph.hasCycleWithLength_mapHom embedding.toHom
    embedding.injective remainingCycle
  exact ctx.avoids
    (target_of_unboundedPowerOfTwoCycle ctx.G.object ambientCycle)

theorem centerDeletedObject_internalThreeCore_free :
    (scope.highCenterDeletionProfile).remainingObject.InternalMinDegreeFree 3 :=
  Graph.External.HegdeSandeepShashank.internalMinDegreeThree_free_of_p13Free
    (scope.highCenterDeletionProfile).remainingObject
    scope.centerDeletedObject_p13Free
    scope.centerDeletedObject_avoidsPowerOfTwoCycle

/-- Exact Type A continuation quantity.  It is computed from the proof-chosen
receiver routing on the literal center-deleted graph. -/
noncomputable def centerDeletedReceiverOverload : Nat :=
  (scope.highCenterDeletionProfile).receiverOverload
    scope.centerDeletedObject_internalThreeCore_free

abbrev CenterDeletedUnsaturated : Prop :=
  (scope.highCenterDeletionProfile).ReceiverUnsaturated
    scope.centerDeletedObject_internalThreeCore_free

/-- Every literal Type B scope satisfies the quantitative bound, regardless
of local-entry resolution and regardless of B2 overlap. -/
theorem neg_netQuarterCharge_le_twentyOne_mul_surplus_add_receiverOverload :
    -scope.highCenterChargeProfile.netQuarterCharge ≤
      21 * (scope.highCenterChargeProfile.assignedSurplus : Int) +
        (scope.centerDeletedReceiverOverload : Int) := by
  exact
    Graph.HighCenterDeletionCharge.Profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload
      scope.highCenterDeletionProfile
      scope.centerDeletedObject_internalThreeCore_free

theorem neg_netQuarterCharge_le_twentyOne_mul_surplus_of_centerDeletedUnsaturated
    (unsaturated : scope.CenterDeletedUnsaturated) :
    -scope.highCenterChargeProfile.netQuarterCharge ≤
      21 * (scope.highCenterChargeProfile.assignedSurplus : Int) := by
  exact
    Graph.HighCenterDeletionCharge.Profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_of_unsaturated
      scope.highCenterDeletionProfile
      scope.centerDeletedObject_internalThreeCore_free
      unsaturated

end TypeBSupportScope

end Erdos64EG.Internal
