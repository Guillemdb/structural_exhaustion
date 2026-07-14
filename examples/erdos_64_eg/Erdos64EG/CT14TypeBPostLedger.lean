import Erdos64EG.CT12TypeBResolution
import Erdos64EG.CT14TypeBBoundaryDeficit
import Erdos64EG.CT14TypeBUnconditionalDeficit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Unconditional post-ledger Type B state space

This file combines the graph-derived high-center resolution with the exact
assigned-charge realization.  A full CT12 choice is not declared successful
merely because its local candidates are disjoint: the theorem continues to
the exact graph-charge split and exposes a negative literal remaining core
when the net charge has not closed.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- Exact, unconditional Type B alternative for a literal support scope.

There are no supplied completeness, charge-safety, or post-ledger fields:
the center family is graph-derived, local resolution is exhaustive, overlap
is the CT12 obstruction, and the last split is the graph-owned charge
identity. -/
theorem unresolved_or_overlap_or_net_nonnegative_or_remaining_negative :
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let support := scope.assignedSupport resolution
        Nonempty support.MinimalOverlap ∨
          ∃ choice : support.completionProfile.FullChoice,
            0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
              support.remainingQuarterCharge choice < 0 := by
  rcases scope.unresolved_or_fullChoice_or_minimalOverlap with
    unresolved | resolved
  · exact Or.inl unresolved
  · right
    rcases resolved with ⟨resolution, choiceOrOverlap⟩
    refine ⟨resolution, ?_⟩
    rcases choiceOrOverlap with choice | overlap
    · right
      let selected := Classical.choice choice
      exact ⟨selected,
        (scope.assignedSupport resolution).netQuarterCharge_nonnegative_or_remaining_negative
          selected⟩
    · exact Or.inl overlap

/-- Fully literal post-ledger state with boundary payment made explicit.
If the local choice exists, the original Type B charge is nonnegative unless
the remaining receiver routing is saturated or the actual deleted-incidence
demand strictly exceeds the exact processed charge reserve.  In the latter
case the negative ledger is quantitatively bounded by assigned surplus. -/
theorem unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload :
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let support := scope.assignedSupport resolution
        Nonempty support.MinimalOverlap ∨
          ∃ choice : support.completionProfile.FullChoice,
            0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
              Nonempty (support.RemainingSaturated choice) ∨
                (support.assignedChargeProfile.netQuarterCharge < 0 ∧
                  support.BoundaryOverload choice ∧
                  Nonempty (support.BoundaryLanding choice) ∧
                  -support.assignedChargeProfile.netQuarterCharge ≤
                    800 *
                      (support.assignedChargeProfile.assignedSurplus : Int)) := by
  rcases scope.unresolved_or_overlap_or_net_nonnegative_or_remaining_negative with
    unresolved | resolved
  · exact Or.inl unresolved
  · right
    rcases resolved with ⟨resolution, overlapOrChoice⟩
    refine ⟨resolution, ?_⟩
    rcases overlapOrChoice with overlap | selected
    · exact Or.inl overlap
    · right
      rcases selected with ⟨choice, netNonnegative | _remainingNegative⟩
      · exact ⟨choice, Or.inl netNonnegative⟩
      · exact ⟨choice,
          TypeBAssignedSupport.net_nonnegative_or_saturated_or_bounded_boundaryOverload
            (scope.assignedSupport resolution) choice⟩

end TypeBSupportScope

/-- Verified endpoint for the exact ordinary Type B state space currently
formalized.  In particular, it does not collapse the negative remaining-core
branch into an unproved success contract. -/
structure VerifiedTypeBPostLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTypeBAssignedChargePrefix ctx
  /-- Choice-free quantitative theorem on the literal scope.  This is the
  official Type B deficit endpoint; local resolution and overlap do not occur
  as hypotheses. -/
  unconditionalDeficit : ∀ scope : TypeBSupportScope ctx,
    -scope.highCenterChargeProfile.netQuarterCharge ≤
      21 * (scope.highCenterChargeProfile.assignedSurplus : Int) +
        (scope.centerDeletedReceiverOverload : Int)
  exactPostLedger : ∀ scope : TypeBSupportScope ctx,
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let support := scope.assignedSupport resolution
        Nonempty support.MinimalOverlap ∨
          ∃ choice : support.completionProfile.FullChoice,
            0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
              support.remainingQuarterCharge choice < 0
  total : ∀ scope : TypeBSupportScope ctx,
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let support := scope.assignedSupport resolution
        Nonempty support.MinimalOverlap ∨
          ∃ choice : support.completionProfile.FullChoice,
            0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
              Nonempty (support.RemainingSaturated choice) ∨
                (support.assignedChargeProfile.netQuarterCharge < 0 ∧
                  support.BoundaryOverload choice ∧
                  Nonempty (support.BoundaryLanding choice) ∧
                  -support.assignedChargeProfile.netQuarterCharge ≤
                    800 *
                      (support.assignedChargeProfile.assignedSurplus : Int))

noncomputable def verifiedTypeBPostLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBAssignedChargePrefix ctx) :
    VerifiedTypeBPostLedgerPrefix ctx where
  previous := previous
  unconditionalDeficit := fun scope =>
    scope.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_receiverOverload
  exactPostLedger := fun scope =>
    scope.unresolved_or_overlap_or_net_nonnegative_or_remaining_negative
  total := fun scope =>
    scope.unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload

theorem exists_verifiedTypeBPostLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBPostLedgerPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTypeBAssignedChargePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBPostLedgerPrefix ctx previous⟩

end Erdos64EG.Internal
