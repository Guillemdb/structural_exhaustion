import Hypostructure.CT1.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT1 reference search

The reference scan is exactly `Core.Finite.Search.run`.  Its branch is chosen
only by `Core.Finite.Search.route`; CT1 merely specializes the generic runner
to its realization predicate and exposes exact inspection accounting.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Execute the canonical counted first-hit scan on the schedule read from
`previous`. -/
def countedScan {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution (capability.scheduleAt previous)
      (spec.Realizes previous)) :=
  Core.Finite.Accounting.countedRun (capability.scheduleAt previous)
    (spec.Realizes previous) (capability.realizesDecidable previous)

/-- The CT1 scan is exactly the value returned by Core finite accounting. -/
def scan {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.scheduleAt previous)
      (spec.Realizes previous) :=
  (countedScan spec capability previous).value

/-- Exact check count of the canonical CT1 scan. -/
def scanChecks {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) : Nat :=
  (countedScan spec capability previous).checks

theorem scanChecks_le_schedule {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    scanChecks spec capability previous <=
      searchCheckBound spec capability.schedule previous :=
  Core.Finite.Accounting.executionChecks_le_card
    (scan spec capability previous)

/-- Core-owned routed result of the exact CT1 scan. -/
abbrev RoutedSearch {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.scheduleAt previous) (spec.Realizes previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.scheduleAt previous) (spec.Realizes previous) =>
      Core.Finite.Search.Avoids (capability.scheduleAt previous)
        (spec.Realizes previous))

/-- Route the completed scan through Core's residual decision executor. -/
def route {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    RoutedSearch spec capability previous :=
  Core.Finite.Search.route (scan spec capability previous)

@[simp] theorem route_scan {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (route spec capability previous).previous = scan spec capability previous :=
  rfl

end Hypostructure.CT1
