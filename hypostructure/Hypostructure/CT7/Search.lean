import Hypostructure.CT7.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT7 exact finite scans

The first scan searches realization.  The second scan is invoked only from
the exact unrealized branch and compares responses on the identical queried
schedule.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Canonical counted realization scan. -/
def countedRealizationScan (capability : Capability spec)
    (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.contextsAt previous)
      (ScheduledRealizes capability previous)) :=
  Core.Finite.Accounting.countedRun (capability.contextsAt previous)
    (ScheduledRealizes capability previous)
    (capability.realizesDecidable previous)

/-- Exact realization search execution. -/
def realizationScan (capability : Capability spec) (previous : Previous) :=
  (countedRealizationScan capability previous).value

/-- Exact visible realization checks. -/
def realizationChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  (countedRealizationScan capability previous).checks

/-- Primitive exact-response mismatch decision. -/
def responseMismatchDecidable (capability : Capability spec)
    (previous : Previous) (coordinate : spec.system.Coordinate) :
    Decidable (ResponseMismatch capability previous coordinate) := by
  letI : DecidableEq spec.system.Value := capability.valueDecEq
  unfold ResponseMismatch
  infer_instance

/-- Canonical counted response-distinction scan. -/
def countedDistinctionScan (capability : Capability spec)
    (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.contextsAt previous)
      (ResponseMismatch capability previous)) :=
  Core.Finite.Accounting.countedRun (capability.contextsAt previous)
    (ResponseMismatch capability previous)
    (responseMismatchDecidable capability previous)

/-- Exact response-distinction search execution. -/
def distinctionScan (capability : Capability spec) (previous : Previous) :=
  (countedDistinctionScan capability previous).value

/-- Exact visible distinction checks. -/
def distinctionChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  (countedDistinctionScan capability previous).checks

/-- Route realization through Core's canonical first-hit decision. -/
def routeRealization (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (realizationScan capability previous)

/-- Route response distinction through Core's canonical first-hit decision. -/
def routeDistinction (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (distinctionScan capability previous)

theorem realizationChecks_le_card (capability : Capability spec)
    (previous : Previous) :
    realizationChecks capability previous ≤
      (capability.contextsAt previous).card :=
  Core.Finite.Accounting.executionChecks_le_card
    (realizationScan capability previous)

theorem distinctionChecks_le_card (capability : Capability spec)
    (previous : Previous) :
    distinctionChecks capability previous ≤
      (capability.contextsAt previous).card :=
  Core.Finite.Accounting.executionChecks_le_card
    (distinctionScan capability previous)

end Hypostructure.CT7
