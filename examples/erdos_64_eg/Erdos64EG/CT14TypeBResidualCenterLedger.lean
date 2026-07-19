import Erdos64EG.CT12DegreeFourB2Routing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Assigned-surplus ledger for ordinary Type B residual centers

This file is the local, finite content of diagram node `[75]`.  Certificate
failures, unresolved B1 entries, and the centers selected by a minimal B2
overlap are all literal members of the already derived high-center set.  The
graph-owned assigned-charge profile proves that each such center has at least
one surplus unit.  Thus every actual residual-center set is charged to the
same assigned surplus, with no global graph enumeration and no assumed
near-cubic estimate.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- Any finite collection of actual scope centers is bounded by the exact
assigned-surplus sum of that scope. -/
theorem residualCenters_card_le_assignedSurplus
    (residualCenters : Finset scope.Center) :
    residualCenters.card ≤ scope.highCenterChargeProfile.assignedSurplus := by
  classical
  have subsetCard : residualCenters.card ≤ scope.highCenters.card := by
    simpa only [scope.centers_card] using
      Core.Enumeration.finset_card_le scope.centers residualCenters
  exact subsetCard.trans
    scope.highCenterDeletionProfile.centers_card_le_assignedSurplus

/-- A node-[80] no-certificate center consumes one real assigned-surplus
unit, and is simultaneously the exact unresolved node-[81] residual. -/
theorem certificateResidual_charged
    (noHigher : scope.NoHigherCenter) (center : scope.Center)
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.UnresolvedCenter ∧
      1 ≤ scope.highCenterChargeProfile.assignedSurplus := by
  refine ⟨scope.certificateResidual_is_unresolved noHigher center residual, ?_⟩
  have singletonBound := scope.residualCenters_card_le_assignedSurplus
    ({center} : Finset scope.Center)
  simpa using singletonBound

/-- Every unresolved local-entry branch contains an actual center and hence
has a real assigned-surplus payer. -/
theorem unresolved_charged (unresolved : scope.UnresolvedCenter) :
    1 ≤ scope.highCenterChargeProfile.assignedSurplus := by
  rcases unresolved with ⟨center, _failure⟩
  have singletonBound := scope.residualCenters_card_le_assignedSurplus
    ({center} : Finset scope.Center)
  simpa using singletonBound

/-- The selected centers of a minimal B2 obstruction are duplicate-free
subschedule data and their total number is bounded by the same assigned
surplus. -/
theorem minimalOverlapCenters_charged
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap) :
    obstruction.selected.length ≤
      scope.highCenterChargeProfile.assignedSurplus := by
  classical
  have fullScheduleLength :
      (scope.assignedSupport resolution).completionProfile.fullSchedule.length =
        (scope.assignedSupport resolution).centers.card := by
    change (scope.assignedSupport resolution).demands.orderedValues.length = _
    rw [FinEnum.orderedValues_length,
      TypeBAssignedSupport.demands_card_eq_centers]
  have selectedBound : obstruction.selected.length ≤
      (scope.assignedSupport resolution).centers.card := by
    calc
      obstruction.selected.length ≤
          (scope.assignedSupport resolution).completionProfile.fullSchedule.length :=
        obstruction.sublist.length_le
      _ = (scope.assignedSupport resolution).centers.card := fullScheduleLength
  have charged := selectedBound.trans
    (scope.assignedSupport resolution).centers_card_le_assignedSurplus
  simpa only [scope.assignedSupport_chargeProfile_eq resolution] using charged

/-- A minimal overlap is nonempty, so its charged center ledger consumes at
least one actual surplus unit. -/
theorem minimalOverlap_has_assignedSurplus
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap) :
    1 ≤ scope.highCenterChargeProfile.assignedSurplus := by
  have positive : 1 ≤ obstruction.selected.length := by
    cases selectedEq : obstruction.selected with
    | nil => exact False.elim (obstruction.nonempty_demands selectedEq)
    | cons head tail => simp
  exact positive.trans (scope.minimalOverlapCenters_charged resolution obstruction)

end TypeBSupportScope

/-- Node-local assigned-surplus obligations. -/
structure VerifiedTypeBResidualCenterLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  anyResidualSet : ∀ (scope : TypeBSupportScope ctx)
    (centers : Finset scope.Center),
      centers.card ≤ scope.highCenterChargeProfile.assignedSurplus
  certificateResidual : ∀ (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) (center : scope.Center),
      scope.FanCertificateResidualCenter noHigher center →
        scope.UnresolvedCenter ∧
          1 ≤ scope.highCenterChargeProfile.assignedSurplus
  overlap : ∀ (scope : TypeBSupportScope ctx)
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap),
      obstruction.selected.length ≤
        scope.highCenterChargeProfile.assignedSurplus

/-- Same-ledger extension of the exact node-[81] CT12 residual. -/
abbrev VerifiedTypeBResidualCenterLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedDegreeFourB2RoutingPrefix ctx)
    (fun _previous => VerifiedTypeBResidualCenterLedger ctx)

noncomputable def verifiedTypeBResidualCenterLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedDegreeFourB2RoutingPrefix ctx) :
    VerifiedTypeBResidualCenterLedgerPrefix ctx :=
  ⟨previous, {
    anyResidualSet := fun scope centers =>
      scope.residualCenters_card_le_assignedSurplus centers
    certificateResidual := fun scope noHigher center residual =>
      scope.certificateResidual_charged noHigher center residual
    overlap := fun scope resolution obstruction =>
      scope.minimalOverlapCenters_charged resolution obstruction
  }⟩

theorem exists_verifiedTypeBResidualCenterLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBResidualCenterLedgerPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedDegreeFourB2RoutingPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBResidualCenterLedgerPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
