import Erdos64EG.CT14TypeBAssignedCharge
import StructuralExhaustion.Graph.LowDegreeReceiverRouting

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Type A discharge of the literal Type B remainder

The post-B2 remainder is not accepted through an abstract charge contract.
This file builds its actual induced graph, proves it remains `P₁₃`-free and
power-of-two-cycle-free, obtains its empty internal three-core from the cited
Hegde--Sandeep--Shashank theorem, and instantiates the framework's exact
`3/7/11` receiver discharge.

All definitions are proof-facing.  In particular, receiver routing is a
noncomputable witness forced by core-freeness; no reachability table, path
family, subset family, or routing-function universe is evaluated.
-/

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

theorem remainingCore_subset_core
    (choice : support.completionProfile.FullChoice) :
    support.remainingCore choice ⊆ support.vertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold remainingCore
  exact Finset.sdiff_subset

theorem remainingCore_subset_remainder
    (choice : support.completionProfile.FullChoice) :
    support.remainingCore choice ⊆ p13RemainderVertices ctx :=
  fun _vertex member => support.vertices_remainder
    (support.remainingCore_subset_core choice member)

/-- Literal graph induced by the unprocessed ordinary core. -/
noncomputable def remainingObject
    (choice : support.completionProfile.FullChoice) :
    Graph.FiniteObject {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
  ctx.G.object.induceFinset (support.remainingCore choice)

/-- The remaining graph embeds inducedly in the verified `P₁₃` remainder. -/
noncomputable def remainingToP13Embedding
    (choice : support.completionProfile.FullChoice) :
    (support.remainingObject choice).graph ↪g (p13Remainder ctx).graph where
  toFun vertex :=
    ⟨vertex.1, support.remainingCore_subset_remainder choice vertex.2⟩
  inj' := by
    intro left right equal
    exact Subtype.ext
      (congrArg (fun vertex : P13RemainderVertex ctx => vertex.1) equal)
  map_rel_iff' := by
    intro left right
    rfl

theorem remainingObject_p13Free
    (choice : support.completionProfile.FullChoice) :
    Graph.InducedPathFree (support.remainingObject choice).graph 13 := by
  intro realization
  rcases realization with ⟨window⟩
  exact p13Remainder_free ctx
    ⟨(support.remainingToP13Embedding choice).comp window⟩

theorem remainingObject_avoidsPowerOfTwoCycle
    (choice : support.completionProfile.FullChoice) :
    ¬Graph.HasCycleWithLength (support.remainingObject choice).graph
      (fun length =>
        ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
  intro remainingCycle
  let embedding := ctx.G.object.induceFinsetEmbedding
    (support.remainingCore choice)
  have ambientCycle := Graph.hasCycleWithLength_mapHom embedding.toHom
    embedding.injective remainingCycle
  exact ctx.avoids
    (target_of_unboundedPowerOfTwoCycle ctx.G.object ambientCycle)

theorem remainingObject_internalThreeCore_free
    (choice : support.completionProfile.FullChoice) :
    (support.remainingObject choice).InternalMinDegreeFree 3 :=
  Graph.External.HegdeSandeepShashank.internalMinDegreeThree_free_of_p13Free
    (support.remainingObject choice)
    (support.remainingObject_p13Free choice)
    (support.remainingObject_avoidsPowerOfTwoCycle choice)

/-- A remaining vertex was not removed as an assigned high center, so the
ambient minimum-degree-three baseline makes its ambient degree exactly three. -/
theorem remainingVertex_ambientDegree_eq_three
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    ctx.G.object.degree vertex.1 = 3 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have remainingMember := vertex.2
  have coreMember := support.remainingCore_subset_core choice remainingMember
  have notProcessed : vertex.1 ∉ support.processedCore choice := by
    exact (Finset.mem_sdiff.mp remainingMember).2
  have notCenter : vertex.1 ∉ support.centers := by
    intro center
    apply notProcessed
    unfold processedCore Graph.AssignedSupportCharge.Profile.processedCore
    exact Finset.mem_union_right _ center
  have notHigh : ¬4 ≤ ctx.G.object.degree vertex.1 := by
    intro high
    apply notCenter
    rw [support.centers_exact]
    exact Finset.mem_filter.mpr ⟨coreMember, high⟩
  have lower : 3 ≤ ctx.G.object.degree vertex.1 :=
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex.1)
  omega

/-- The induced remaining graph is subcubic because every one of its vertices
has ambient degree exactly three. -/
theorem remainingObject_degree_le_three
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    (support.remainingObject choice).degree vertex ≤ 3 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  let remaining := support.remainingObject choice
  change remaining.degree vertex ≤ 3
  have imageSubset :
      Subtype.val '' remaining.graph.neighborSet vertex ⊆
        ctx.G.object.graph.neighborSet vertex.1 := by
    rintro neighbor ⟨subneighbor, adjacent, rfl⟩
    exact adjacent
  have degreeLe : remaining.degree vertex ≤
      ctx.G.object.degree vertex.1 := by
    rw [remaining.degree_eq_ncard_neighborSet,
      ctx.G.object.degree_eq_ncard_neighborSet]
    calc
      (remaining.graph.neighborSet vertex).ncard =
          (Subtype.val '' remaining.graph.neighborSet vertex).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (ctx.G.object.graph.neighborSet vertex.1).ncard :=
        Set.ncard_le_ncard imageSubset
  have ambient := support.remainingVertex_ambientDegree_eq_three choice vertex
  omega

noncomputable def remainingSubcubicProfile
    (choice : support.completionProfile.FullChoice) :
    Graph.LowDegreeReceiverRouting.SubcubicProfile
      (support.remainingObject choice) where
  degree_le_three := support.remainingObject_degree_le_three choice
  coreFree := support.remainingObject_internalThreeCore_free choice

@[simp]
theorem remainingDischargeInput_degree
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    (support.remainingSubcubicProfile choice).dischargeInput.degree vertex =
      (support.remainingObject choice).degree vertex :=
  rfl

noncomputable def remainingNeighborCount
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) : Nat := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  exact (ctx.G.object.graph.neighborFinset vertex.1 ∩
    support.remainingCore choice).card

/-- Induced degree in the remaining graph is exactly the number of ambient
neighbours which remain after the B-ledger deletion. -/
theorem remainingObject_degree_eq_remainingNeighborCount
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    (support.remainingObject choice).degree vertex =
      support.remainingNeighborCount choice vertex := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  let remaining := support.remainingObject choice
  rw [remaining.degree_eq_ncard_neighborSet]
  have neighborImage :
      Subtype.val '' remaining.graph.neighborSet vertex =
        ctx.G.object.graph.neighborSet vertex.1 ∩
          ↑(support.remainingCore choice) := by
    ext neighbor
    constructor
    · rintro ⟨subneighbor, adjacent, rfl⟩
      exact ⟨adjacent, subneighbor.2⟩
    · rintro ⟨adjacent, member⟩
      exact ⟨⟨neighbor, member⟩, adjacent, rfl⟩
  calc
    (remaining.graph.neighborSet vertex).ncard =
        (Subtype.val '' remaining.graph.neighborSet vertex).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = (ctx.G.object.graph.neighborSet vertex.1 ∩
          ↑(support.remainingCore choice)).ncard := by rw [neighborImage]
    _ = (ctx.G.object.graph.neighborFinset vertex.1 ∩
          support.remainingCore choice).card := by
      rw [← Set.ncard_coe_finset
        (ctx.G.object.graph.neighborFinset vertex.1 ∩
          support.remainingCore choice)]
      congr 1
      ext neighbor
      simp
    _ = support.remainingNeighborCount choice vertex := by
      rfl

noncomputable def originalNeighborCount
    (vertex : ctx.G.Vertex) : Nat := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  exact (ctx.G.object.graph.neighborFinset vertex ∩ support.vertices).card

theorem internalDegree_eq_originalNeighborCount (vertex : ctx.G.Vertex) :
    support.assignedChargeProfile.internalDegree vertex =
      support.originalNeighborCount vertex := by
  rfl

/-- Deleting processed vertices can only decrease internal degree.  This is
the precise direction needed to audit the attempted Type B-to-Type A handoff. -/
theorem remainingObject_degree_le_originalInternalDegree
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    (support.remainingObject choice).degree vertex ≤
      support.assignedChargeProfile.internalDegree vertex.1 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  rw [support.remainingObject_degree_eq_remainingNeighborCount choice vertex,
    support.internalDegree_eq_originalNeighborCount]
  unfold remainingNeighborCount originalNeighborCount
  apply Finset.card_le_card
  intro neighbor member
  rw [Finset.mem_inter] at member ⊢
  exact ⟨member.1, support.remainingCore_subset_core choice member.2⟩

theorem originalInternalDegree_le_three
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    support.assignedChargeProfile.internalDegree vertex.1 ≤ 3 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  have cardLe :
      (ctx.G.object.graph.neighborFinset vertex.1 ∩ support.vertices).card ≤
        (ctx.G.object.graph.neighborFinset vertex.1).card :=
    Finset.card_le_card Finset.inter_subset_left
  have ambient := support.remainingVertex_ambientDegree_eq_three choice vertex
  rw [support.internalDegree_eq_originalNeighborCount]
  unfold originalNeighborCount
  calc
    (ctx.G.object.graph.neighborFinset vertex.1 ∩ support.vertices).card ≤
        (ctx.G.object.graph.neighborFinset vertex.1).card := cardLe
    _ = ctx.G.object.degree vertex.1 := by rfl
    _ = 3 := ambient

/-- Number of original-core incidences lost when the selected B-ledger
vertices and high centers are deleted. -/
noncomputable def remainingBoundaryLoss
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) : Nat :=
  support.assignedChargeProfile.internalDegree vertex.1 -
    (support.remainingObject choice).degree vertex

/-- Pointwise exact boundary-transfer identity.  The induced Type A charge is
the retained original-core charge plus four quarter-units for every deleted
original-core incidence. -/
theorem inducedQuarterChargeAt_eq_original_add_boundary
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    4 * ((3 - (support.remainingObject choice).degree vertex : Nat) : Int) - 1 =
      support.assignedChargeProfile.coreQuarterChargeAt vertex.1 +
        4 * (support.remainingBoundaryLoss choice vertex : Int) := by
  have degreeLe :=
    support.remainingObject_degree_le_originalInternalDegree choice vertex
  have internalLe := support.originalInternalDegree_le_three choice vertex
  unfold remainingBoundaryLoss
    Graph.AssignedSupportCharge.Profile.coreQuarterChargeAt
    Graph.AssignedSupportCharge.Profile.positiveDeficiencyAt
  omega

noncomputable def remainingInducedQuarterCharge
    (choice : support.completionProfile.FullChoice) : Int :=
  ∑ vertex ∈
      (support.remainingSubcubicProfile choice).dischargeInput.support,
    (support.remainingSubcubicProfile choice).dischargeInput.quarterCharge
      vertex

noncomputable def remainingBoundaryCredit
    (choice : support.completionProfile.FullChoice) : Int :=
  4 * ∑ vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice},
    (support.remainingBoundaryLoss choice vertex : Int)

theorem remainingInducedQuarterCharge_eq_raw_add_boundary
    (choice : support.completionProfile.FullChoice) :
    support.remainingInducedQuarterCharge choice =
      support.remainingQuarterCharge choice +
        support.remainingBoundaryCredit choice := by
  letI : FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices
  letI : DecidableEq {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices.decEq
  unfold remainingInducedQuarterCharge remainingBoundaryCredit
  rw [show
    (support.remainingSubcubicProfile choice).dischargeInput.support =
      (Finset.univ : Finset {vertex : ctx.G.Vertex //
        vertex ∈ support.remainingCore choice}) by
      ext vertex
      simp [Graph.LowDegreeReceiverRouting.SubcubicProfile.dischargeInput]]
  simp only [Core.FiniteReceiverDischarge.Input.quarterCharge]
  simp only [support.remainingDischargeInput_degree choice]
  simp_rw [support.inducedQuarterChargeAt_eq_original_add_boundary choice]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold remainingQuarterCharge
  rw [Finset.sum_coe_sort]

/-- The framework receiver theorem computes the induced-core charge, not the
raw pre-deletion charge retained in the Type B identity. -/
theorem remainingDischargeSum_eq_inducedQuarterCharge
    (choice : support.completionProfile.FullChoice) :
    (∑ vertex ∈
        (support.remainingSubcubicProfile choice).dischargeInput.support,
        (support.remainingSubcubicProfile choice).dischargeInput.quarterCharge
          vertex) = support.remainingInducedQuarterCharge choice := by
  rfl

abbrev RemainingUnsaturated
    (choice : support.completionProfile.FullChoice) : Prop :=
  (support.remainingSubcubicProfile choice).Unsaturated

/-- Literal remaining receiver whose routed cubic fibre exceeds its exact
degree-dependent capacity. -/
abbrev RemainingSaturated
    (choice : support.completionProfile.FullChoice) :=
  (support.remainingSubcubicProfile choice).Saturated

theorem not_remainingUnsaturated_iff_saturated
    (choice : support.completionProfile.FullChoice) :
    ¬support.RemainingUnsaturated choice ↔
      Nonempty (support.RemainingSaturated choice) :=
  Graph.LowDegreeReceiverRouting.SubcubicProfile.not_unsaturated_iff_nonempty_saturated
    (support.remainingSubcubicProfile choice)

theorem remainingSaturated_threshold_le_load
    (choice : support.completionProfile.FullChoice)
    (saturated : support.RemainingSaturated choice) :
    4 * (3 - (support.remainingObject choice).degree saturated.receiver) ≤
      (support.remainingSubcubicProfile choice).dischargeRouting.load
        saturated.receiver := by
  exact saturated.threshold_le_load

/-- Every cubic vertex in the literal overloaded fibre is graph-reachable to
the displayed saturated receiver. -/
theorem remainingSaturated_load_reachable
    (choice : support.completionProfile.FullChoice)
    (saturated : support.RemainingSaturated choice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice})
    (loaded : vertex ∈
      (support.remainingSubcubicProfile choice).dischargeRouting.loadSet
        saturated.receiver) :
    (support.remainingObject choice).graph.Reachable vertex
      saturated.receiver := by
  let profile := support.remainingSubcubicProfile choice
  have loadedParts :=
    (Core.FiniteReceiverDischarge.Routing.mem_loadSet_iff
      profile.dischargeRouting saturated.receiver vertex).1 loaded
  let cubic : {vertex // vertex ∈ profile.dischargeInput.cubicSet} :=
    ⟨vertex, loadedParts.1⟩
  have reachable := profile.dischargeRouting_reachable cubic
  have routeEq : (profile.dischargeRouting.route cubic).1 =
      saturated.receiver := by
    have routed := loadedParts.2
    simpa [Core.FiniteReceiverDischarge.Routing.routeVertex,
      loadedParts.1, cubic] using routed
  rw [routeEq] at reachable
  exact reachable

/-- Exact conclusion of unsaturated Type A discharging after a B-ledger
deletion: raw retained charge plus the deleted-boundary credit is
nonnegative. -/
theorem raw_add_boundary_nonnegative_of_unsaturated
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice) :
    0 ≤ support.remainingQuarterCharge choice +
      support.remainingBoundaryCredit choice := by
  rw [← support.remainingInducedQuarterCharge_eq_raw_add_boundary choice]
  rw [← support.remainingDischargeSum_eq_inducedQuarterCharge choice]
  exact (support.remainingSubcubicProfile choice).quarterCharge_nonnegative unsaturated

/-- Honest unsaturated split: either the retained raw term is already
nonnegative, or the positive deleted-boundary credit is an additional proof
obligation. -/
theorem remaining_nonnegative_or_boundary_transfer_required
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice) :
    0 ≤ support.remainingQuarterCharge choice ∨
      (support.remainingQuarterCharge choice < 0 ∧
        0 < support.remainingBoundaryCredit choice) := by
  have adjusted := support.raw_add_boundary_nonnegative_of_unsaturated choice
    unsaturated
  by_cases raw : 0 ≤ support.remainingQuarterCharge choice
  · exact Or.inl raw
  · right
    omega

end TypeBAssignedSupport

end Erdos64EG.Internal
