import Hypostructure.CT13.State
import Hypostructure.Core.Residual.Decision

/-!
# CT13 canonical searches and Core routing

Core owns the primary first-hit decision, the resource-overlap decision, and
the final deficit comparison.  Both finite scans inspect only schedules read
from the literal predecessor.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource uAlpha

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

/-- First-hit certificates over one duplicate-free schedule have the same
canonical index. -/
private theorem indexedHit_index_eq {α : Type uAlpha}
    {schedule : Core.Finite.Enumeration α} {predicate : α -> Prop}
    (left right : Core.Finite.Search.IndexedHit schedule predicate) :
    left.index = right.index := by
  apply Fin.ext
  by_contra unequal
  rcases lt_or_gt_of_ne unequal with leftBefore | rightBefore
  · have leftInPrefix :
        left.value ∈ schedule.values.take right.index.1 := by
      letI : DecidableEq α := schedule.decEq
      change schedule.values.get left.index ∈
        schedule.values.take right.index.1
      rw [List.mem_take_iff_idxOf_lt (List.get_mem _ _)]
      rw [List.get_idxOf schedule.nodup]
      exact leftBefore
    exact (right.first left.value leftInPrefix) left.sound
  · have rightInPrefix :
        right.value ∈ schedule.values.take left.index.1 := by
      letI : DecidableEq α := schedule.decEq
      change schedule.values.get right.index ∈
        schedule.values.take left.index.1
      rw [List.mem_take_iff_idxOf_lt (List.get_mem _ _)]
      rw [List.get_idxOf schedule.nodup]
      exact rightBefore
    exact (left.first right.value rightInPrefix) right.sound

/-- Counted canonical tier-one payer scan. -/
def countedTierOneScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.payersAt previous) (spec.Eligible previous)) :=
  Core.Finite.Accounting.countedRun (capability.payersAt previous)
    (spec.Eligible previous) (capability.eligibleDecidable previous)

/-- Proof-carrying canonical tier-one payer scan. -/
def tierOneScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.payersAt previous)
      (spec.Eligible previous) :=
  (countedTierOneScan capability previous).value

/-- Core-owned tier-one-found versus exhaustive-absence route. -/
abbrev RoutedTierOne (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.payersAt previous) (spec.Eligible previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.payersAt previous) (spec.Eligible previous) =>
      TierOneAbsenceState capability previous)

/-- Route the exact primary scan through Core. -/
def routeTierOne (capability : Capability spec) (previous : Previous) :
    RoutedTierOne capability previous :=
  Core.Finite.Search.route (tierOneScan capability previous)

/-- A generated tier-one hit pays exactly its inspected prefix. -/
theorem countedTierOneScan_checks_eq_hit (capability : Capability spec)
    (previous : Previous)
    (hasHit : (countedTierOneScan capability previous).value.HasHit) :
    (countedTierOneScan capability previous).checks =
      ((countedTierOneScan capability previous).value.hitOfHasHit
        hasHit).index.1 + 1 := by
  simp only [countedTierOneScan, Core.Finite.Accounting.countedRun]
  cases found : (Core.Finite.Search.run
      (capability.payersAt previous) (spec.Eligible previous)
      (capability.eligibleDecidable previous)).hit? with
  | none =>
      have impossible : False := by
        change (Core.Finite.Search.run
          (capability.payersAt previous) (spec.Eligible previous)
          (capability.eligibleDecidable previous)).hit?.isSome = true at hasHit
        rw [found] at hasHit
        simp at hasHit
      exact impossible.elim
  | some hit =>
      have selectedIndex :
          ((Core.Finite.Search.run
            (capability.payersAt previous) (spec.Eligible previous)
            (capability.eligibleDecidable previous)).hitOfHasHit
              hasHit).index = hit.index :=
        indexedHit_index_eq _ _
      simpa [selectedIndex] using
        (Core.Finite.Accounting.executionChecks_of_hit
          (Core.Finite.Search.run
            (capability.payersAt previous) (spec.Eligible previous)
            (capability.eligibleDecidable previous)) hit found)

/-- Exhaustive tier-one absence charges the complete predecessor-owned payer
schedule. -/
theorem countedTierOneScan_checks_eq_card_of_absence
    (capability : Capability spec) (previous : Previous)
    (absence : TierOneAbsenceState capability previous) :
    (countedTierOneScan capability previous).checks =
      (capability.payersAt previous).card := by
  have missed : (countedTierOneScan capability previous).value.hit? = none := by
    apply (Core.Finite.Search.hit?_eq_none_iff
      (capability.payersAt previous) (spec.Eligible previous)
      (capability.eligibleDecidable previous)).mpr
    intro payer member eligible
    obtain ⟨index, indexed⟩ :=
      ((capability.payersAt previous).mem_iff_exists_index payer).mp member
    exact absence index (by simpa [indexed] using eligible)
  change Core.Finite.Accounting.executionChecks
    (countedTierOneScan capability previous).value =
      (capability.payersAt previous).card
  exact Core.Finite.Accounting.executionChecks_of_miss
    (countedTierOneScan capability previous).value missed

/-- Canonical minimum-fallback computation with its exact number of strict
cost comparisons. -/
def countedComputeFallback (capability : Capability spec)
    (previous : Previous) (absence : TierOneAbsenceState capability previous) :
    Core.Counted (FallbackState capability previous) :=
  ⟨computeFallback capability previous absence,
    (capability.obstructionsAt previous).comparisonCount⟩

@[simp] theorem countedComputeFallback_checks (capability : Capability spec)
    (previous : Previous) (absence : TierOneAbsenceState capability previous) :
    (countedComputeFallback capability previous absence).checks =
      (capability.obstructionsAt previous).comparisonCount :=
  rfl

/-- Primitive decision for one resource-overlap pair. -/
def resourceOverlapDecidable (capability : Capability spec)
    (previous : Previous) (fallback : FallbackState capability previous)
    (pair : spec.Payer previous × spec.Payer previous) :
    Decidable (ResourceOverlap (spec := spec) previous pair) := by
  letI : DecidableEq (spec.Payer previous) :=
    (selectedTierTwo capability previous fallback).decEq
  letI : DecidableEq (spec.Resource previous) :=
    capability.resourceDecidableEq previous
  unfold ResourceOverlap
  exact inferInstance

/-- Counted canonical pairwise overlap scan. -/
def countedOverlapScan (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    Core.Counted (Core.Finite.Search.Execution
      (reconciliationPairs capability previous fallback)
      (ResourceOverlap (spec := spec) previous)) :=
  Core.Finite.Accounting.countedRun
    (reconciliationPairs capability previous fallback)
    (ResourceOverlap (spec := spec) previous)
    (resourceOverlapDecidable capability previous fallback)

/-- Proof-carrying canonical pairwise overlap scan. -/
def overlapScan (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    Core.Finite.Search.Execution
      (reconciliationPairs capability previous fallback)
      (ResourceOverlap (spec := spec) previous) :=
  (countedOverlapScan capability previous fallback).value

/-- Core-owned overlap versus clean-reconciliation route. -/
abbrev RoutedOverlap (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (reconciliationPairs capability previous fallback)
        (ResourceOverlap (spec := spec) previous) => execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (reconciliationPairs capability previous fallback)
        (ResourceOverlap (spec := spec) previous) =>
      OverlapFreeState capability previous fallback)

/-- Route the exact resource-overlap scan through Core. -/
def routeOverlap (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    RoutedOverlap capability previous fallback :=
  Core.Finite.Search.route (overlapScan capability previous fallback)

/-- A generated overlap pays exactly its inspected pair prefix. -/
theorem countedOverlapScan_checks_eq_hit (capability : Capability spec)
    (previous : Previous) (fallback : FallbackState capability previous)
    (hasHit : (countedOverlapScan capability previous fallback).value.HasHit) :
    (countedOverlapScan capability previous fallback).checks =
      ((countedOverlapScan capability previous fallback).value.hitOfHasHit
        hasHit).index.1 + 1 := by
  simp only [countedOverlapScan, Core.Finite.Accounting.countedRun]
  cases found : (Core.Finite.Search.run
      (reconciliationPairs capability previous fallback)
      (ResourceOverlap (spec := spec) previous)
      (resourceOverlapDecidable capability previous fallback)).hit? with
  | none =>
      have impossible : False := by
        change (Core.Finite.Search.run
          (reconciliationPairs capability previous fallback)
          (ResourceOverlap (spec := spec) previous)
          (resourceOverlapDecidable capability previous fallback)).hit?.isSome =
            true at hasHit
        rw [found] at hasHit
        simp at hasHit
      exact impossible.elim
  | some hit =>
      have selectedIndex :
          ((Core.Finite.Search.run
            (reconciliationPairs capability previous fallback)
            (ResourceOverlap (spec := spec) previous)
            (resourceOverlapDecidable capability previous fallback)).hitOfHasHit
              hasHit).index = hit.index :=
        indexedHit_index_eq _ _
      simpa [selectedIndex] using
        (Core.Finite.Accounting.executionChecks_of_hit
          (Core.Finite.Search.run
            (reconciliationPairs capability previous fallback)
            (ResourceOverlap (spec := spec) previous)
            (resourceOverlapDecidable capability previous fallback)) hit found)

/-- Clean reconciliation charges the complete canonical pair schedule. -/
theorem countedOverlapScan_checks_eq_card_of_clean
    (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous)
    (clean : OverlapFreeState capability previous fallback) :
    (countedOverlapScan capability previous fallback).checks =
      (reconciliationPairs capability previous fallback).card := by
  have missed :
      (countedOverlapScan capability previous fallback).value.hit? = none := by
    apply (Core.Finite.Search.hit?_eq_none_iff
      (reconciliationPairs capability previous fallback)
      (ResourceOverlap (spec := spec) previous)
      (resourceOverlapDecidable capability previous fallback)).mpr
    intro pair member overlap
    obtain ⟨index, indexed⟩ :=
      ((reconciliationPairs capability previous fallback).mem_iff_exists_index
        pair).mp member
    exact clean index (by simpa [indexed] using overlap)
  change Core.Finite.Accounting.executionChecks
    (countedOverlapScan capability previous fallback).value =
      (reconciliationPairs capability previous fallback).card
  exact Core.Finite.Accounting.executionChecks_of_miss
    (countedOverlapScan capability previous fallback).value missed

/-- Build the canonical reconciliation ledger once, charging one construction
step per selected tier-two payer. -/
def countedBuildReconciliationLedger (capability : Capability spec)
    (previous : Previous) (fallback : FallbackState capability previous)
    (overlapFree : OverlapFreeState capability previous fallback) :
    Core.Counted (ReconciliationLedger capability previous) :=
  ⟨buildReconciliationLedger capability previous fallback overlapFree,
    (selectedTierTwo capability previous fallback).card⟩

@[simp] theorem countedBuildReconciliationLedger_checks
    (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous)
    (overlapFree : OverlapFreeState capability previous fallback) :
    (countedBuildReconciliationLedger capability previous fallback
      overlapFree).checks =
        (selectedTierTwo capability previous fallback).card :=
  rfl

/-- Core decision node for charge deficit versus reconciled coverage. -/
def comparisonNode (capability : Capability spec) (previous : Previous) :
    Core.Residual.Decision.Node
      (ReconciliationLedger capability previous)
      (fun ledger => ledger.capacity < spec.demand previous)
      (fun ledger => spec.demand previous <= ledger.capacity) :=
  Core.Residual.Decision.Node.create
    (fun ledger => Nat.decLt ledger.capacity (spec.demand previous))
    (by
      intro ledger notDeficit
      exact Nat.le_of_not_gt notDeficit)

/-- Core-owned final comparison route. -/
abbrev RoutedComparison (capability : Capability spec)
    (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun ledger : ReconciliationLedger capability previous =>
      ledger.capacity < spec.demand previous)
    (fun ledger : ReconciliationLedger capability previous =>
      spec.demand previous <= ledger.capacity)

/-- Compare reconciled charge with demand through Core. -/
def compare (capability : Capability spec) (previous : Previous)
    (ledger : ReconciliationLedger capability previous) :
    RoutedComparison capability previous :=
  (comparisonNode capability previous).run ledger

/-- Retain the exact capacity comparison used to select the final terminal and
charge that one arithmetic decision exactly once. -/
def countedCompare (capability : Capability spec) (previous : Previous)
    (ledger : ReconciliationLedger capability previous) :
    Core.Counted (RoutedComparison capability previous) :=
  ⟨compare capability previous ledger, 1⟩

@[simp] theorem countedCompare_checks (capability : Capability spec)
    (previous : Previous) (ledger : ReconciliationLedger capability previous) :
    (countedCompare capability previous ledger).checks = 1 :=
  rfl

@[simp] theorem countedCompare_previous (capability : Capability spec)
    (previous : Previous) (ledger : ReconciliationLedger capability previous) :
    (countedCompare capability previous ledger).value.previous = ledger :=
  rfl

end Hypostructure.CT13
