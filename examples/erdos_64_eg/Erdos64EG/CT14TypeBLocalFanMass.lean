import Erdos64EG.CT14TypeBResidualCenterLedger
import StructuralExhaustion.Graph.SelectedSurplusMass
import StructuralExhaustion.Graph.SupportIndexedFanMass

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Repaired local endpoint at diagram node [84]

The frozen predecessors justify a local statement for one literal Type B
scope.  They do not justify the manuscript's later aggregation over a
canonical family of ordinary and grouped supports.  This module therefore
executes exactly the local statement and gives the unavailable global family
producer a separate downstream type.

For an exact selected set of actual high centers, CT14 assigns cost one to
each selected center and capacity `degree - 3` to that same center.  Positivity
is derived from membership in the graph-computed high-center schedule.  The
runner scans only that schedule.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

def centerSurplus (center : scope.Center) : Nat :=
  ctx.G.object.degree center.1 - 3

theorem centerSurplus_positive (center : scope.Center) :
    1 ≤ scope.centerSurplus center := by
  unfold centerSurplus
  have high := scope.center_high center
  omega

noncomputable def localFanMassProfile (selected : Finset scope.Center) :
    Graph.SelectedSurplusMass.Profile scope.Center := by
  classical
  exact {
    items := scope.centers
    Selected := fun center => center ∈ selected
    selectedDecidable := fun center => inferInstance
    surplus := scope.centerSurplus
    positive := scope.centerSurplus_positive
  }

abbrev LocalFanMassStage (selected : Finset scope.Center) :=
  (scope.localFanMassProfile selected).VerifiedStage ctx.toBranchContext

noncomputable def localFanMassStage (selected : Finset scope.Center) :
    scope.LocalFanMassStage selected :=
  (scope.localFanMassProfile selected).verifiedStage ctx.toBranchContext

/-- Conservative equality-comparison ledger for the list-backed selected-set
membership tests.  Each of the four CT14 item scans may inspect the complete
selected set. -/
noncomputable def localFanMassExpandedChecks
    (selected : Finset scope.Center) : Nat :=
  4 * scope.centers.card * (selected.card + 1) + 1

theorem localFanMassExpandedChecks_quadratic
    (selected : Finset scope.Center) :
    scope.localFanMassExpandedChecks selected ≤
      5 * (scope.centers.card + 1) ^ 2 := by
  letI : FinEnum scope.Center := scope.centers
  have selectedBound : selected.card ≤ scope.centers.card := by
    calc
      selected.card ≤ Fintype.card scope.Center := Finset.card_le_univ selected
      _ = scope.centers.card := by rw [FinEnum.card_eq_fintypeCard]
  unfold localFanMassExpandedChecks
  nlinarith

theorem localFanMass_selectedCount_eq_card (selected : Finset scope.Center) :
    (scope.localFanMassProfile selected).selectedCount = selected.card := by
  classical
  letI : FinEnum scope.Center := scope.centers
  unfold Graph.SelectedSurplusMass.Profile.selectedCount
    Graph.SelectedSurplusMass.Profile.lowerAt localFanMassProfile
  simpa using (Finset.sum_boole (R := Nat)
    (fun center : scope.Center => center ∈ selected)
    (Finset.univ : Finset scope.Center))

theorem localFanMass_totalSurplus_eq_assignedSurplus
    (selected : Finset scope.Center) :
    (scope.localFanMassProfile selected).totalSurplus =
      scope.highCenterChargeProfile.assignedSurplus := by
  letI : FinEnum scope.Center := scope.centers
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold Graph.SelectedSurplusMass.Profile.totalSurplus
    localFanMassProfile centerSurplus
    Graph.AssignedSupportCharge.Profile.assignedSurplus
    Graph.AssignedSupportCharge.Profile.surplusAt
    highCenterChargeProfile
  symm
  exact Finset.sum_subtype scope.highCenters (fun _ => Iff.rfl)
    (fun center => ctx.G.object.degree center - 3)

/-- Exact CT14 payload for one predecessor-supplied local center set. -/
structure LocalFanMass (selected : Finset scope.Center) : Prop where
  stage : scope.LocalFanMassStage selected
  countExact :
    (scope.localFanMassProfile selected).selectedCount = selected.card
  surplusExact :
    (scope.localFanMassProfile selected).totalSurplus =
      scope.highCenterChargeProfile.assignedSurplus
  charged : selected.card ≤ scope.highCenterChargeProfile.assignedSurplus
  work : (scope.localFanMassProfile selected).checks =
    4 * scope.centers.card + 1
  expandedWork : scope.localFanMassExpandedChecks selected =
    4 * scope.centers.card * (selected.card + 1) + 1
  quadraticWork : scope.localFanMassExpandedChecks selected ≤
    5 * (scope.centers.card + 1) ^ 2

noncomputable def localFanMass (selected : Finset scope.Center) :
    scope.LocalFanMass selected where
  stage := scope.localFanMassStage selected
  countExact := scope.localFanMass_selectedCount_eq_card selected
  surplusExact := scope.localFanMass_totalSurplus_eq_assignedSurplus selected
  charged := by
    rw [← scope.localFanMass_selectedCount_eq_card selected,
      ← scope.localFanMass_totalSurplus_eq_assignedSurplus selected]
    exact (scope.localFanMassStage selected).localBound
  work := rfl
  expandedWork := rfl
  quadraticWork := scope.localFanMassExpandedChecks_quadratic selected

/-! ## Exact incoming-edge connectors for node `[84]`

These lemmas do not add a fourth branch to the manuscript.  They expose the
local CT14 payload carried by each of the three existing edges into `[84]`.
In particular, every selected center is an element of the predecessor's
actual `highCenters` subtype; no ambient vertex set or family of graphs is
enumerated.
-/

/-- The node-`[80]` certificate-failure edge supplies its literal center,
the node-`[81]` unresolved residual derived from that failure, and the exact
singleton fan mass charged to the scope's assigned surplus. -/
theorem certificateFailure_localFanMass
    (noHigher : scope.NoHigherCenter) (center : scope.Center)
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.UnresolvedCenter ∧ scope.LocalFanMass {center} := by
  exact ⟨scope.certificateResidual_is_unresolved noHigher center residual,
    scope.localFanMass {center}⟩

/-- The direct unresolved edge out of node `[81]` retains a concrete missing
center and therefore supplies the exact singleton fan-mass payload expected
by node `[84]`. -/
theorem unresolved_localFanMass
    (unresolved : scope.UnresolvedCenter) :
    ∃ center : scope.Center,
      (¬Nonempty (scope.LocalEntryAt center)) ∧
        scope.LocalFanMass {center} := by
  rcases unresolved with ⟨center, missing⟩
  exact ⟨center, missing, scope.localFanMass {center}⟩

/-- Exact selected center set of a minimal overlap.  `Demand` and
`scope.Center` are definitionally the same subtype because `assignedSupport`
retains `scope.highCenters`. -/
noncomputable def overlapCenters
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap) :
    Finset scope.Center := by
  classical
  exact obstruction.selected.toFinset

theorem mem_overlapCenters_iff
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap)
    (center : scope.Center) :
    center ∈ scope.overlapCenters resolution obstruction ↔
      center ∈ obstruction.selected := by
  classical
  change center ∈ obstruction.selected.toFinset ↔
    center ∈ obstruction.selected
  exact List.mem_toFinset

theorem overlapCenters_card_eq_selected_length
    (resolution : scope.FullResolution)
    (obstruction : (scope.assignedSupport resolution).MinimalOverlap) :
    (scope.overlapCenters resolution obstruction).card =
      obstruction.selected.length := by
  classical
  unfold overlapCenters
  apply List.toFinset_card_of_nodup
  exact obstruction.sublist.nodup
    (scope.assignedSupport resolution).demands.nodup_orderedValues

/-- The node-`[83]` minimal-overlap edge supplies fan mass on exactly its
duplicate-free selected-center schedule.  The selected-cardinality equality
is part of `LocalFanMass.countExact` together with
`overlapCenters_card_eq_selected_length`; no replacement center set is used.
-/
theorem minimalOverlap_localFanMass
    (noHigher : scope.NoHigherCenter)
    (result : scope.B2MinimalOverlap noHigher) :
    scope.LocalFanMass
      (scope.overlapCenters result.resolution result.obstruction) :=
  scope.localFanMass
    (scope.overlapCenters result.resolution result.obstruction)

/-- The strongest branch-total local result available from nodes
`[75]`, `[81]`, `[82]`, and `[83]`. -/
inductive LocalFanMassRoute (noHigher : scope.NoHigherCenter) : Prop
  | unresolved (center : scope.Center)
      (missing : ¬Nonempty (scope.LocalEntryAt center))
      (mass : scope.LocalFanMass {center})
  | nonnegative (result : scope.B2Nonnegative noHigher)
  | route8 (result : scope.B2RemainingNegative noHigher)
  | overlap (result : scope.B2MinimalOverlap noHigher)
      (mass : scope.LocalFanMass
        (scope.overlapCenters result.resolution result.obstruction))

noncomputable def localFanMassRoute (noHigher : scope.NoHigherCenter) :
    scope.LocalFanMassRoute noHigher := by
  cases route : scope.degreeFourB2Route noHigher with
  | unresolved residual =>
      let center : scope.Center := Classical.choose residual
      have missing : ¬Nonempty (scope.LocalEntryAt center) :=
        Classical.choose_spec residual
      exact .unresolved center missing (scope.localFanMass {center})
  | nonnegative result =>
      exact .nonnegative result
  | remainingNegative result =>
      exact .route8 result
  | minimalOverlap result =>
      exact .overlap result
        (scope.localFanMass
          (scope.overlapCenters result.resolution result.obstruction))

end TypeBSupportScope

/-- Green local endpoint replacing the over-strong reading of node `[84]`.
Its predecessor field is the exact node-[75] endpoint, which itself retains
nodes `[81]`--`[83]`. -/
structure VerifiedTypeBLocalFanMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTypeBResidualCenterLedgerPrefix ctx
  route : ∀ (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter), scope.LocalFanMassRoute noHigher

noncomputable def verifiedTypeBLocalFanMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBResidualCenterLedgerPrefix ctx) :
    VerifiedTypeBLocalFanMassPrefix ctx where
  previous := previous
  route := fun scope noHigher => scope.localFanMassRoute noHigher

theorem exists_verifiedTypeBLocalFanMassPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBLocalFanMassPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTypeBResidualCenterLedgerPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBLocalFanMassPrefix ctx previous⟩

/-! ## Separate downstream global aggregate frontier -/

/-- A downstream producer must construct the actual support-indexed family
and prove its semantic coefficient and within-role incidence properties.
There is intentionally no constructor from `VerifiedTypeBLocalFanMassPrefix`:
the local node-84 theorem neither assumes nor implies this contract. -/
structure TypeBGlobalFanMassProducer
    (Support Center Occurrence : Type*) where
  profile : Graph.SupportIndexedFanMass.Profile Support Center Occurrence
  coefficientExact : profile.coefficient = 208

/-- The downstream aggregate theorem is available once its genuine producer
exists.  This theorem does not create or assume such a producer. -/
theorem globalFanMass_bound_of_producer
    {Support Center Occurrence : Type*}
    (producer : TypeBGlobalFanMassProducer Support Center Occurrence) :
    producer.profile.residualMass ≤
      416 * producer.profile.globalSurplus := by
  simpa [producer.coefficientExact] using
    producer.profile.residualMass_le_two_mul_coefficient_mul_globalSurplus

end Erdos64EG.Internal
