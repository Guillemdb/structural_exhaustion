import Hypostructure.CT14.State
import Hypostructure.Core.Residual.Decision

/-!
# CT14 reference scans and decisions

Core performs both ordered first-hit scans and the final arithmetic decision.
The scans inspect only the exact schedule queried from the predecessor.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uMember, uLabel} Previous}

/-- Primitive decision that one optional capacity is unavailable. -/
def missingCapacityDecidable (previous : Previous)
    (member : spec.Member previous) :
    Decidable (spec.memberCapacity previous member = none) := by
  cases value : spec.memberCapacity previous member with
  | none => exact .isTrue rfl
  | some capacity =>
      exact .isFalse (by
        intro impossible
        cases impossible)

/-- Primitive decision that one optional label is unavailable. -/
def missingLabelDecidable (previous : Previous)
    (member : spec.Member previous) :
    Decidable (spec.memberLabel previous member = none) := by
  cases value : spec.memberLabel previous member with
  | none => exact .isTrue rfl
  | some label =>
      exact .isFalse (by
        intro impossible
        cases impossible)

/-- Counted canonical missing-capacity scan. -/
def countedCapacityScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.membersAt previous)
      (fun member => spec.memberCapacity previous member = none)) :=
  Core.Finite.Accounting.countedRun (capability.membersAt previous)
    (fun member => spec.memberCapacity previous member = none)
    (missingCapacityDecidable previous)

/-- Proof-carrying canonical missing-capacity scan. -/
def capacityScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.membersAt previous)
      (fun member => spec.memberCapacity previous member = none) :=
  (countedCapacityScan capability previous).value

/-- Core-owned capacity-availability route. -/
abbrev RoutedCapacity (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.membersAt previous)
        (fun member => spec.memberCapacity previous member = none) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.membersAt previous)
        (fun member => spec.memberCapacity previous member = none) =>
      CapacityComplete capability previous)

/-- Route the exact missing-capacity scan through Core. -/
def routeCapacity (capability : Capability spec) (previous : Previous) :
    RoutedCapacity capability previous :=
  Core.Finite.Search.route (capacityScan capability previous)

/-- Counted canonical missing-label scan. -/
def countedLabelScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.membersAt previous)
      (fun member => spec.memberLabel previous member = none)) :=
  Core.Finite.Accounting.countedRun (capability.membersAt previous)
    (fun member => spec.memberLabel previous member = none)
    (missingLabelDecidable previous)

/-- Proof-carrying canonical missing-label scan. -/
def labelScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.membersAt previous)
      (fun member => spec.memberLabel previous member = none) :=
  (countedLabelScan capability previous).value

/-- Core-owned label-availability route. -/
abbrev RoutedLabel (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.membersAt previous)
        (fun member => spec.memberLabel previous member = none) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.membersAt previous)
        (fun member => spec.memberLabel previous member = none) =>
      LabelComplete capability previous)

/-- Route the exact missing-label scan through Core. -/
def routeLabel (capability : Capability spec) (previous : Previous) :
    RoutedLabel capability previous :=
  Core.Finite.Search.route (labelScan capability previous)

/-- Core decision node for aggregate overload versus available capacity. -/
def comparisonNode (capability : Capability spec) (previous : Previous) :
    Core.Residual.Decision.Node
      (AggregateLedger capability previous)
      (fun ledger => AggregateCertificate capability previous ledger)
      (fun ledger => CapacityResidual capability previous ledger) :=
  Core.Residual.Decision.Node.create
    (fun ledger => Nat.decLt ledger.capacity.total ledger.lower.total)
    (by
      intro ledger notExceeded
      omega)

/-- Core-owned aggregate comparison route. -/
abbrev RoutedComparison (capability : Capability spec)
    (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun ledger : AggregateLedger capability previous =>
      AggregateCertificate capability previous ledger)
    (fun ledger : AggregateLedger capability previous =>
      CapacityResidual capability previous ledger)

/-- Compare the generated aggregate ledger through Core. -/
def compare (capability : Capability spec) (previous : Previous)
    (ledger : AggregateLedger capability previous) :
    RoutedComparison capability previous :=
  (comparisonNode capability previous).run ledger

end Hypostructure.CT14
