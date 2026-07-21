import Hypostructure.CT6.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT6 generated residual states

Both residuals are computed from the queried predecessor order.  Their
constructors are private, so applications cannot select a terminal or author
an active ledger independently of the canonical scan.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uIndex, uData} Previous}

/-- Ordered contribution entries on the exact incoming schedule. -/
def activeEntries (capability : Capability spec) (previous : Previous) :
    List (spec.Index previous × Nat) :=
  (capability.failureOrderAt previous).values.map fun index =>
    (index, spec.contribution previous index)

/-- Framework-computed contribution total for an exhaustive active pass. -/
def activeTotal (capability : Capability spec) (previous : Previous) : Nat :=
  (activeEntries capability previous).map Prod.snd |>.sum

/-- Canonical first failure, including its exact clean prefix and local data. -/
structure FirstFailureResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  hit : Core.Finite.Search.IndexedHit
    (capability.failureOrderAt previous) (spec.Failure previous)
  data : spec.FailureData previous hit.value
  data_exact : data = spec.failureData previous hit.value hit.holds

/-- Build the unique CT6 diagnostic payload from a Core-produced first hit. -/
def firstFailureOfHit (capability : Capability spec) (previous : Previous)
    (hit : Core.Finite.Search.IndexedHit
      (capability.failureOrderAt previous) (spec.Failure previous)) :
    FirstFailureResidual capability previous :=
  .mk hit (spec.failureData previous hit.value hit.holds) rfl

/-- Exhaustive active ledger generated from Core's exact avoidance proof. -/
structure ActiveLedgerResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  entries : List (spec.Index previous × Nat)
  entries_exact : entries = activeEntries capability previous
  total : Nat
  total_exact : total = activeTotal capability previous
  noFailure : Core.Finite.Search.Avoids
    (capability.failureOrderAt previous) (spec.Failure previous)

/-- Compute the active ledger from the complementary Core search branch. -/
def buildActiveLedger (capability : Capability spec) (previous : Previous)
    (noFailure : Core.Finite.Search.Avoids
      (capability.failureOrderAt previous) (spec.Failure previous)) :
    ActiveLedgerResidual capability previous :=
  .mk (activeEntries capability previous) rfl
    (activeTotal capability previous) rfl noFailure

end Hypostructure.CT6
