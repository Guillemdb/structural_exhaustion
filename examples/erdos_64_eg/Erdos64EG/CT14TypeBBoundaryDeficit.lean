import Erdos64EG.CT14TypeBBoundaryTransfer
import Erdos64EG.CT14TypeBSupportSize

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Quantitative closure of the Type B boundary branch

The failed boundary-transfer branch is not left as an assumption.  The
literal cut is bounded by the ambient degree sum on its processed side.  The
processed Type B support contains at most twenty-five vertices per assigned
center, each of ambient degree at most eight.  Consequently the deleted
boundary credit is at most eight hundred quarter-units per center, hence at
most eight hundred times the assigned surplus.

All bounds are proofs about supplied finite sets.  No family of subsets,
matchings, transfer functions, or graph configurations is enumerated.
-/

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

/-- The literal induced-boundary loss is exactly the sum used by the Type A
remainder correction. -/
theorem inducedBoundary_totalLoss_eq_remainingBoundaryLoss
    (choice : support.completionProfile.FullChoice) :
    (support.inducedBoundaryProfile choice).totalLoss =
      ∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        support.remainingBoundaryLoss choice vertex := by
  letI : FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices
  letI : DecidableEq {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold Graph.FiniteInducedBoundary.Profile.totalLoss
  rw [support.inducedBoundary_remaining choice]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro vertex _member
  exact support.inducedBoundary_loss_eq_remainingBoundaryLoss choice
    vertex

/-- The complete deleted-incidence count is at most `200` per assigned
center. -/
theorem remainingBoundaryLoss_sum_le_twoHundred_mul_centers
    (choice : support.completionProfile.FullChoice) :
    (∑ vertex : {vertex : ctx.G.Vertex //
        vertex ∈ support.remainingCore choice},
      support.remainingBoundaryLoss choice vertex) ≤
        200 * support.centers.card := by
  rw [← support.inducedBoundary_totalLoss_eq_remainingBoundaryLoss choice]
  exact (support.inducedBoundaryProfile choice).totalLoss_le_processedDegreeSum.trans
    (support.processedDegreeSum_le_twoHundred_mul_centers choice)

/-- In quarter-units the boundary correction is at most `800` per assigned
center. -/
theorem remainingBoundaryCredit_le_eightHundred_mul_centers
    (choice : support.completionProfile.FullChoice) :
    support.remainingBoundaryCredit choice ≤
      800 * (support.centers.card : Int) := by
  have natural :=
    support.remainingBoundaryLoss_sum_le_twoHundred_mul_centers choice
  have castBound :
      (∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        (support.remainingBoundaryLoss choice vertex : Int)) ≤
          200 * (support.centers.card : Int) := by
    exact_mod_cast natural
  unfold remainingBoundaryCredit
  calc
    4 * ∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        (support.remainingBoundaryLoss choice vertex : Int) ≤
        4 * (200 * (support.centers.card : Int)) := by omega
    _ = 800 * (support.centers.card : Int) := by ring

/-- Every assigned center contributes at least one unit of assigned surplus,
so the boundary correction is bounded solely by the ledger's surplus mass. -/
theorem remainingBoundaryCredit_le_eightHundred_mul_assignedSurplus
    (choice : support.completionProfile.FullChoice) :
    support.remainingBoundaryCredit choice ≤
      800 * (support.assignedChargeProfile.assignedSurplus : Int) := by
  have centerBound := support.centers_card_le_assignedSurplus
  have centerBoundInt :
      (support.centers.card : Int) ≤
        (support.assignedChargeProfile.assignedSurplus : Int) := by
    exact_mod_cast centerBound
  exact (support.remainingBoundaryCredit_le_eightHundred_mul_centers choice).trans
    (by omega)

/-- Unsaturated Type A discharging bounds the negative part of the original
Type B net ledger by the actual deleted-boundary credit. -/
theorem neg_netQuarterCharge_le_remainingBoundaryCredit_of_unsaturated
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice) :
    -support.assignedChargeProfile.netQuarterCharge ≤
      support.remainingBoundaryCredit choice := by
  have adjusted := support.raw_add_boundary_nonnegative_of_unsaturated
    choice unsaturated
  have reserveNonnegative := support.processedQuarterReserve_nonnegative choice
  rw [support.netQuarterCharge_eq_processedReserve_add_remaining choice]
  omega

/-- Fully proved quantitative Type B deficit bound in the unsaturated branch.
No boundary-transfer hypothesis remains. -/
theorem neg_netQuarterCharge_le_eightHundred_mul_assignedSurplus_of_unsaturated
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice) :
    -support.assignedChargeProfile.netQuarterCharge ≤
      800 * (support.assignedChargeProfile.assignedSurplus : Int) :=
  (support.neg_netQuarterCharge_le_remainingBoundaryCredit_of_unsaturated
      choice unsaturated).trans
    (support.remainingBoundaryCredit_le_eightHundred_mul_assignedSurplus choice)

/-- Exact unconditional endpoint for an ordinary assigned Type B support.
Either the ledger is nonnegative, an actual receiver is saturated, or a
strictly negative ledger has a literal overloaded cut with a literal landing
and its deficit is bounded by `800` times assigned surplus. -/
theorem net_nonnegative_or_saturated_or_bounded_boundaryOverload
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
      Nonempty (support.RemainingSaturated choice) ∨
        (support.assignedChargeProfile.netQuarterCharge < 0 ∧
          support.BoundaryOverload choice ∧
          Nonempty (support.BoundaryLanding choice) ∧
          -support.assignedChargeProfile.netQuarterCharge ≤
            800 *
              (support.assignedChargeProfile.assignedSurplus : Int)) := by
  by_cases unsaturated : support.RemainingUnsaturated choice
  · by_cases nonnegative :
        0 ≤ support.assignedChargeProfile.netQuarterCharge
    · exact Or.inl nonnegative
    · have negative :
          support.assignedChargeProfile.netQuarterCharge < 0 := by omega
      rcases (support.boundaryTransferProfile choice).transfer_or_overloaded with
        transfer | overload
      · have closed :=
          support.netQuarterCharge_nonnegative_of_unsaturated_boundaryTransfer
            choice unsaturated transfer.some
        omega
      · exact Or.inr (Or.inr
          ⟨negative, overload,
            support.boundaryOverload_has_landing choice overload,
            support.neg_netQuarterCharge_le_eightHundred_mul_assignedSurplus_of_unsaturated
              choice unsaturated⟩)
  · exact Or.inr (Or.inl
      ((support.not_remainingUnsaturated_iff_saturated choice).1 unsaturated))

end TypeBAssignedSupport

end Erdos64EG.Internal
