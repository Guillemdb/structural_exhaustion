import Hypostructure.CT6.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT6 executable capability

The monitored order is a typed query into the literal predecessor.  CT6 does
not accept an ambient enumeration or a detached application-built schedule.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

/-- Worst-case primitive checks for one ordered failure scan. -/
def localCheckBound {Index : Type uIndex}
    (order : Core.Finite.Enumeration Index) : Nat :=
  order.card

/-- Minimum author input for executable ordered-activity analysis. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uIndex, uData} Previous) where
  failureOrder : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Index previous)
  failureDecidable : (previous : Previous) ->
    (index : spec.Index previous) -> Decidable (spec.Failure previous index)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (failureOrder.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uIndex, uData} Previous}

/-- Exact residual-owned order at one predecessor. -/
def failureOrderAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Index previous) :=
  capability.failureOrder.read previous

/-- Framework-visible polynomial envelope for the complete CT6 pass. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.failureOrderAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT6
