import Hypostructure.CT9.State
import Hypostructure.Core.Residual.Decision

/-!
# CT9 deterministic overload search

Core scans the complete authored label schedule from left to right.  Each
predicate evaluation computes one exact fibre from the predecessor-owned item
schedule and compares it with the authored capacity.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}

/-- Primitive decidable overload comparison for one generated fibre. -/
def overloadedDecidable {capability : Capability spec}
    {previous : Previous} (partition : Partition capability previous)
    (label : spec.Label previous) :
    Decidable (Overloaded capability previous partition label) :=
  Nat.decLt _ _

/-- Counted canonical first-overload scan.  Core's count records inspected
labels; complete CT9 accounting additionally charges one full item scan and
one comparison for each inspected label. -/
def countedOverloadScan (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.labelScheduleAt previous)
      (Overloaded capability previous partition)) :=
  Core.Finite.Accounting.countedRun (capability.labelScheduleAt previous)
    (Overloaded capability previous partition)
    (overloadedDecidable partition)

/-- Proof-carrying canonical first-overload scan. -/
def overloadScan (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :
    Core.Finite.Search.Execution (capability.labelScheduleAt previous)
      (Overloaded capability previous partition) :=
  (countedOverloadScan capability previous partition).value

/-- Core-owned overload-versus-bounded route. -/
abbrev RoutedOverload (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.labelScheduleAt previous)
        (Overloaded capability previous partition) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.labelScheduleAt previous)
        (Overloaded capability previous partition) =>
      AvoidsOverload capability previous partition)

/-- Route the exact first-overload scan through Core. -/
def routeOverload (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :
    RoutedOverload capability previous partition :=
  Core.Finite.Search.route (overloadScan capability previous partition)

end Hypostructure.CT9
