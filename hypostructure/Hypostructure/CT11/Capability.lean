import Hypostructure.CT11.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT11 executable capability

Both the ordered cells and their strict-negative total certificate are typed
queries into the literal predecessor.  An invocation cannot replace either
with an ambient enumeration or a detached decomposition.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

/-- Worst-case primitive checks: one complete admissibility scan followed by
one complete local-budget scan. -/
def localCheckBound {Cell : Type uCell}
    (cells : Core.Finite.Enumeration Cell) : Nat :=
  2 * cells.card

/-- Minimal executable author surface for CT11. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCell} Previous) where
  cells : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Cell previous)
  admissibleDecidable : (previous : Previous) ->
    (cell : spec.Cell previous) -> Decidable (spec.Admissible previous cell)
  negativeTotal : Core.Residual.Query Previous fun previous =>
    ((cells.read previous).values.map
      (spec.localBudget previous)).sum < 0
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (cells.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCell} Previous}

/-- Exact residual-owned cell order at one predecessor. -/
def cellsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Cell previous) :=
  capability.cells.read previous

/-- Registered strict-negative total for the exact queried order. -/
theorem negativeTotalAt (capability : Capability spec)
    (previous : Previous) :
    ((capability.cellsAt previous).values.map
      (spec.localBudget previous)).sum < 0 :=
  capability.negativeTotal.read previous

/-- Framework-visible polynomial envelope for the complete two-pass scan. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.cellsAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT11
