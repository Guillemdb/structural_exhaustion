import Hypostructure.CT13.State
import Hypostructure.Core.Residual.Decision

/-!
# CT13 canonical searches and Core routing

Core owns the primary first-hit decision, the resource-overlap decision, and
the final deficit comparison.  Both finite scans inspect only schedules read
from the literal predecessor.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

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

end Hypostructure.CT13
