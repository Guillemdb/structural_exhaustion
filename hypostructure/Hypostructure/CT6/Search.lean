import Hypostructure.CT6.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT6 canonical ordered search

Core performs one counted first-hit scan and routes its two exhaustive
outcomes.  CT6 contributes only the local failure predicate and decider.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uIndex, uData} Previous}

/-- Counted canonical first-failure scan. -/
def countedActivityScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.failureOrderAt previous) (spec.Failure previous)) :=
  Core.Finite.Accounting.countedRun (capability.failureOrderAt previous)
    (spec.Failure previous) (capability.failureDecidable previous)

/-- Proof-carrying canonical first-failure scan. -/
def activityScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution
      (capability.failureOrderAt previous) (spec.Failure previous) :=
  (countedActivityScan capability previous).value

/-- Core-owned hit-versus-exhaustive-activity route. -/
abbrev RoutedActivity (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.failureOrderAt previous) (spec.Failure previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.failureOrderAt previous) (spec.Failure previous) =>
      Core.Finite.Search.Avoids
        (capability.failureOrderAt previous) (spec.Failure previous))

/-- Route the exact residual-owned activity scan through Core. -/
def routeActivity (capability : Capability spec) (previous : Previous) :
    RoutedActivity capability previous :=
  Core.Finite.Search.route (activityScan capability previous)

end Hypostructure.CT6
