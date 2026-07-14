import Mathlib.Tactic
import StructuralExhaustion.Graph.AssignedSupportCharge
import StructuralExhaustion.Graph.FiniteInducedBoundary
import StructuralExhaustion.Graph.LowDegreeReceiverRouting

namespace StructuralExhaustion.Graph.HighCenterDeletionCharge

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Charge after deleting all high centers

This is the reusable quantitative core of the Type B to Type A transition.
All assigned high centers are deleted at once.  The retained graph is
subcubic, and any negative induced charge is recorded by the literal receiver
overload from `FiniteReceiverDischarge`.  The difference between raw support
charge and induced charge is the actual center cut.

The resulting bound does not require a choice of pairwise-disjoint local fan
entries.  Hence local-entry failure and carrier overlap cannot disappear into
an unproved B2 contract.  The construction scans only supplied vertex and
edge finsets; it does not enumerate subsets, routings, or graph families.
-/

variable {V : Type u} {object : Graph.FiniteObject V}

/-- Literal assigned support whose noncenters have ambient degree three and
whose assigned centers have ambient degree at least four. -/
structure Profile (object : Graph.FiniteObject V) where
  charge : Graph.AssignedSupportCharge.Profile object
  centers_subset_core : charge.assignedCenters ⊆ charge.core
  center_high : ∀ center ∈ charge.assignedCenters, 4 ≤ object.degree center
  noncenter_degree_eq_three : ∀ vertex ∈ charge.core,
    vertex ∉ charge.assignedCenters → object.degree vertex = 3

namespace Profile

variable (profile : Profile object)

noncomputable def remainingCore : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact profile.charge.core \ profile.charge.assignedCenters

noncomputable def remainingObject :
    Graph.FiniteObject {vertex : V // vertex ∈ profile.remainingCore} :=
  object.induceFinset profile.remainingCore

noncomputable def boundaryProfile :
    Graph.FiniteInducedBoundary.Profile object where
  whole := profile.charge.core
  processed := profile.charge.assignedCenters
  processed_subset_whole := profile.centers_subset_core

@[simp]
theorem boundary_remaining :
    profile.boundaryProfile.remaining = profile.remainingCore := by
  rfl

theorem remainingObject_degree_le_three
    (vertex : {vertex : V // vertex ∈ profile.remainingCore}) :
    profile.remainingObject.degree vertex ≤ 3 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have imageSubset :
      Subtype.val '' profile.remainingObject.graph.neighborSet vertex ⊆
        object.graph.neighborSet vertex.1 := by
    rintro neighbor ⟨subneighbor, adjacent, rfl⟩
    exact adjacent
  have degreeLe : profile.remainingObject.degree vertex ≤
      object.degree vertex.1 := by
    rw [profile.remainingObject.degree_eq_ncard_neighborSet,
      object.degree_eq_ncard_neighborSet]
    calc
      (profile.remainingObject.graph.neighborSet vertex).ncard =
          (Subtype.val ''
            profile.remainingObject.graph.neighborSet vertex).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (object.graph.neighborSet vertex.1).ncard :=
        Set.ncard_le_ncard imageSubset
  have member := Finset.mem_sdiff.mp vertex.2
  have ambient := profile.noncenter_degree_eq_three vertex.1 member.1 member.2
  omega

noncomputable def subcubicProfile
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3) :
    Graph.LowDegreeReceiverRouting.SubcubicProfile profile.remainingObject where
  degree_le_three := profile.remainingObject_degree_le_three
  coreFree := coreFree

/-- Actual Type A continuation mass left after deleting all high centers. -/
noncomputable def receiverOverload
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3) : Nat :=
  (profile.subcubicProfile coreFree).totalOverload

abbrev ReceiverUnsaturated
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3) : Prop :=
  (profile.subcubicProfile coreFree).Unsaturated

theorem receiverOverload_eq_zero_of_unsaturated
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3)
    (unsaturated : profile.ReceiverUnsaturated coreFree) :
    profile.receiverOverload coreFree = 0 :=
  Graph.LowDegreeReceiverRouting.SubcubicProfile.totalOverload_eq_zero_of_unsaturated
    (profile.subcubicProfile coreFree) unsaturated

theorem remainingObject_degree_eq_remainingNeighborCount
    (vertex : {vertex : V // vertex ∈ profile.remainingCore}) :
    profile.remainingObject.degree vertex =
      profile.boundaryProfile.remainingNeighborCount vertex.1 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [profile.remainingObject.degree_eq_ncard_neighborSet]
  have neighborImage :
      Subtype.val '' profile.remainingObject.graph.neighborSet vertex =
        object.graph.neighborSet vertex.1 ∩ ↑profile.remainingCore := by
    ext neighbor
    constructor
    · rintro ⟨subneighbor, adjacent, rfl⟩
      exact ⟨adjacent, subneighbor.2⟩
    · rintro ⟨adjacent, member⟩
      exact ⟨⟨neighbor, member⟩, adjacent, rfl⟩
  calc
    (profile.remainingObject.graph.neighborSet vertex).ncard =
        (Subtype.val ''
          profile.remainingObject.graph.neighborSet vertex).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = (object.graph.neighborSet vertex.1 ∩
          ↑profile.remainingCore).ncard := by rw [neighborImage]
    _ = (object.graph.neighborFinset vertex.1 ∩
          profile.remainingCore).card := by
      rw [← Set.ncard_coe_finset
        (object.graph.neighborFinset vertex.1 ∩ profile.remainingCore)]
      congr 1
      ext neighbor
      simp
    _ = profile.boundaryProfile.remainingNeighborCount vertex.1 := by
      rfl

theorem internalDegree_eq_wholeNeighborCount (vertex : V) :
    profile.charge.internalDegree vertex =
      profile.boundaryProfile.wholeNeighborCount vertex := by
  rfl

noncomputable def rawRemainingQuarterCharge : Int :=
  ∑ vertex ∈ profile.remainingCore.attach,
    profile.charge.coreQuarterChargeAt vertex

noncomputable def inducedRemainingQuarterCharge : Int :=
  ∑ vertex ∈ profile.remainingCore.attach,
    (4 * ((3 - profile.remainingObject.degree vertex : Nat) : Int) - 1)

noncomputable def boundaryQuarterCredit : Int :=
  4 * ∑ vertex ∈ profile.remainingCore.attach,
    (profile.boundaryProfile.loss vertex : Int)

theorem inducedQuarterChargeAt_eq_raw_add_boundary
    (vertex : {vertex : V // vertex ∈ profile.remainingCore}) :
    4 * ((3 - profile.remainingObject.degree vertex : Nat) : Int) - 1 =
      profile.charge.coreQuarterChargeAt vertex.1 +
        4 * (profile.boundaryProfile.loss vertex.1 : Int) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have remainingLeWhole :=
    profile.boundaryProfile.remainingNeighborCount_le_wholeNeighborCount
      vertex.1
  have wholeLeThree :
      profile.boundaryProfile.wholeNeighborCount vertex.1 ≤ 3 := by
    rw [← profile.internalDegree_eq_wholeNeighborCount]
    unfold Graph.AssignedSupportCharge.Profile.internalDegree
    have cardLe :
        (object.graph.neighborFinset vertex.1 ∩
          profile.charge.core).card ≤
            (object.graph.neighborFinset vertex.1).card :=
      Finset.card_le_card Finset.inter_subset_left
    have member := Finset.mem_sdiff.mp vertex.2
    have ambient := profile.noncenter_degree_eq_three vertex.1 member.1 member.2
    exact cardLe.trans_eq ambient
  rw [profile.remainingObject_degree_eq_remainingNeighborCount vertex]
  unfold Graph.AssignedSupportCharge.Profile.coreQuarterChargeAt
    Graph.AssignedSupportCharge.Profile.positiveDeficiencyAt
    Graph.FiniteInducedBoundary.Profile.loss
  rw [profile.internalDegree_eq_wholeNeighborCount]
  omega

theorem inducedRemaining_eq_raw_add_boundary :
    profile.inducedRemainingQuarterCharge =
      profile.rawRemainingQuarterCharge + profile.boundaryQuarterCredit := by
  letI : FinEnum {vertex : V // vertex ∈ profile.remainingCore} :=
    profile.remainingObject.input.vertices
  letI : DecidableEq {vertex : V // vertex ∈ profile.remainingCore} :=
    profile.remainingObject.input.vertices.decEq
  letI : DecidableEq V := object.input.vertices.decEq
  unfold inducedRemainingQuarterCharge rawRemainingQuarterCharge
    boundaryQuarterCredit
  calc
    (∑ vertex ∈ profile.remainingCore.attach,
        (4 * ((3 - profile.remainingObject.degree vertex : Nat) : Int) - 1)) =
        ∑ vertex ∈ profile.remainingCore.attach,
          (profile.charge.coreQuarterChargeAt vertex +
            4 * (profile.boundaryProfile.loss vertex : Int)) := by
      exact Finset.sum_congr
        (s₁ := profile.remainingCore.attach)
        (s₂ := profile.remainingCore.attach) rfl
        (fun vertex _member =>
        profile.inducedQuarterChargeAt_eq_raw_add_boundary vertex)
    _ = (∑ vertex ∈ profile.remainingCore.attach,
          profile.charge.coreQuarterChargeAt vertex) +
        4 * ∑ vertex ∈ profile.remainingCore.attach,
          (profile.boundaryProfile.loss vertex : Int) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem neg_inducedRemaining_le_receiverOverload
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3) :
    -profile.inducedRemainingQuarterCharge ≤
      (profile.receiverOverload coreFree : Int) := by
  let subcubic := profile.subcubicProfile coreFree
  have bound := subcubic.neg_quarterCharge_le_totalOverload
  have supportEq : subcubic.dischargeInput.support =
      (Finset.univ : Finset {vertex : V // vertex ∈ profile.remainingCore}) := by
    ext vertex
    simp [Graph.LowDegreeReceiverRouting.SubcubicProfile.dischargeInput]
  have sumEq :
      (∑ vertex ∈ subcubic.dischargeInput.support,
        subcubic.dischargeInput.quarterCharge vertex) =
          profile.inducedRemainingQuarterCharge := by
    rw [supportEq]
    unfold inducedRemainingQuarterCharge
    rw [show
      (Finset.univ : Finset {vertex : V // vertex ∈ profile.remainingCore}) =
        profile.remainingCore.attach by
      ext vertex
      simp]
    exact Finset.sum_congr
      (s₁ := profile.remainingCore.attach)
      (s₂ := profile.remainingCore.attach) rfl
      (fun vertex _member => by
        change
          4 * ((3 - profile.remainingObject.degree vertex : Nat) : Int) - 1 =
            4 * ((3 - profile.remainingObject.degree vertex : Nat) : Int) - 1
        rfl)
  rw [sumEq] at bound
  simpa [receiverOverload, subcubic] using bound

theorem centers_card_le_assignedSurplus :
    profile.charge.assignedCenters.card ≤
      profile.charge.assignedSurplus := by
  unfold Graph.AssignedSupportCharge.Profile.assignedSurplus
  calc
    profile.charge.assignedCenters.card =
        ∑ _center ∈ profile.charge.assignedCenters, 1 := by simp
    _ ≤ ∑ center ∈ profile.charge.assignedCenters,
        Graph.AssignedSupportCharge.Profile.surplusAt object center := by
      apply Finset.sum_le_sum
      intro center member
      have high := profile.center_high center member
      unfold Graph.AssignedSupportCharge.Profile.surplusAt
      omega

theorem centerDegreeSum_le_four_mul_assignedSurplus :
    (∑ center ∈ profile.charge.assignedCenters, object.degree center) ≤
      4 * profile.charge.assignedSurplus := by
  unfold Graph.AssignedSupportCharge.Profile.assignedSurplus
  calc
    (∑ center ∈ profile.charge.assignedCenters, object.degree center) ≤
        ∑ center ∈ profile.charge.assignedCenters,
          4 * Graph.AssignedSupportCharge.Profile.surplusAt object center := by
      apply Finset.sum_le_sum
      intro center member
      have high := profile.center_high center member
      unfold Graph.AssignedSupportCharge.Profile.surplusAt
      omega
    _ = 4 * ∑ center ∈ profile.charge.assignedCenters,
        Graph.AssignedSupportCharge.Profile.surplusAt object center := by
      rw [Finset.mul_sum]

theorem boundaryQuarterCredit_le_sixteen_mul_assignedSurplus :
    profile.boundaryQuarterCredit ≤
      16 * (profile.charge.assignedSurplus : Int) := by
  have lossBound := profile.boundaryProfile.totalLoss_le_processedDegreeSum
  have degreeBound := profile.centerDegreeSum_le_four_mul_assignedSurplus
  have natural : profile.boundaryProfile.totalLoss ≤
      4 * profile.charge.assignedSurplus := lossBound.trans degreeBound
  have castBound : (profile.boundaryProfile.totalLoss : Int) ≤
      4 * (profile.charge.assignedSurplus : Int) := by
    exact_mod_cast natural
  have creditEq : profile.boundaryQuarterCredit =
      4 * (profile.boundaryProfile.totalLoss : Int) := by
    unfold boundaryQuarterCredit Graph.FiniteInducedBoundary.Profile.totalLoss
    rw [profile.boundary_remaining]
    push_cast
    exact congrArg (fun value : Int => 4 * value)
      (Finset.sum_attach profile.remainingCore
        (fun vertex => (profile.boundaryProfile.loss vertex : Int)))
  rw [creditEq]
  omega

theorem netQuarterCharge_eq_centers_add_remaining :
    profile.charge.netQuarterCharge =
      profile.charge.centerQuarterCharge +
        ((∑ center ∈ profile.charge.assignedCenters,
          profile.charge.coreQuarterChargeAt center) +
            (profile.charge.assignedCenters.card : Int)) +
        profile.rawRemainingQuarterCharge := by
  have identity :=
    profile.charge.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
      ∅ (by simp) profile.centers_subset_core (by simp)
  simpa [rawRemainingQuarterCharge, Finset.sum_attach, remainingCore,
    Graph.AssignedSupportCharge.Profile.remainingCore,
    Graph.AssignedSupportCharge.Profile.processedCore] using identity

/-- Unconditional high-center-deletion bound.  All Type B loss is charged to
actual assigned surplus plus the literal Type A receiver overload; no local
fan choice, disjointness hypothesis, or boundary-payment field occurs. -/
theorem neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3) :
    -profile.charge.netQuarterCharge ≤
      21 * (profile.charge.assignedSurplus : Int) +
        (profile.receiverOverload coreFree : Int) := by
  have inducedBound := profile.neg_inducedRemaining_le_receiverOverload coreFree
  rw [profile.inducedRemaining_eq_raw_add_boundary] at inducedBound
  have boundaryBound :=
    profile.boundaryQuarterCredit_le_sixteen_mul_assignedSurplus
  have centerCardBoundNat := profile.centers_card_le_assignedSurplus
  have centerCardBound :
      (profile.charge.assignedCenters.card : Int) ≤
        (profile.charge.assignedSurplus : Int) := by
    exact_mod_cast centerCardBoundNat
  have centerCorrection := profile.charge.centerCoreCharge_add_card_nonnegative
  have identity := profile.netQuarterCharge_eq_centers_add_remaining
  have centerCharge := profile.charge.centerQuarterCharge_eq
  omega

theorem neg_netQuarterCharge_le_twentyOne_mul_surplus_of_unsaturated
    (coreFree : profile.remainingObject.InternalMinDegreeFree 3)
    (unsaturated : profile.ReceiverUnsaturated coreFree) :
    -profile.charge.netQuarterCharge ≤
      21 * (profile.charge.assignedSurplus : Int) := by
  have bound :=
    profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload coreFree
  rw [profile.receiverOverload_eq_zero_of_unsaturated coreFree unsaturated] at bound
  simpa using bound

end Profile

end StructuralExhaustion.Graph.HighCenterDeletionCharge
