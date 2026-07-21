import Hypostructure.CT9.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT9 executable capability

The item schedule is read from the literal predecessor.  The label schedule
is a complete authored finite universe because CT9's bounded terminal is a
statement about every label.  Applications cannot supply fibres, a selected
label, a bounded partition, or routing data.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

/-- Worst-case primitive work.  Every inspected label scans the complete item
schedule once and then performs one capacity comparison. -/
def localCheckBound {Item : Type uItem} {Label : Type uLabel}
    (items : Core.Finite.Enumeration Item)
    (labels : Core.Finite.Enumeration Label) : Nat :=
  labels.card * (items.card + 1)

/-- Minimal author-facing CT9 capability. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous) where
  items : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Item previous)
  labels : (previous : Previous) ->
    Core.Finite.CompleteEnumeration (spec.Label previous)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (items.read previous) (labels previous).toEnumeration <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}

/-- Exact residual-owned item schedule. -/
def itemsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Item previous) :=
  capability.items.read previous

/-- Exact complete label search order. -/
def labelsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.CompleteEnumeration (spec.Label previous) :=
  capability.labels previous

/-- Enumeration view used by Core's deterministic search. -/
def labelScheduleAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Label previous) :=
  (capability.labelsAt previous).toEnumeration

/-- Framework-visible polynomial envelope for the complete partition scan. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous =>
    localCheckBound (capability.itemsAt previous)
      (capability.labelScheduleAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT9
