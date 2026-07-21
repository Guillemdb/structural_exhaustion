import Hypostructure.CT15.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT15 executable capability

The sole finite coordinate schedule is a typed query into the exact incoming
ledger.  Applications provide primitive dependence decisions and a polynomial
bound for the framework's prescribed local scan.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

/-- Worst-case primitive decisions: one complete rank pass, one complete
first-drop pass, and one capacity comparison on the full-rank branch. -/
def localCheckBound {Coordinate : Type uCoordinate}
    (coordinates : Core.Finite.Enumeration Coordinate) : Nat :=
  2 * coordinates.card + 1

/-- Minimal executable CT15 surface.  In particular, it contains no rank,
ledger, outcome, or route supplied by an application. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate} Previous) where
  coordinates : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Coordinate previous)
  targetDependentDecidable : (previous : Previous) ->
    (coordinate : spec.Coordinate previous) ->
      Decidable (spec.TargetDependent previous coordinate)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (coordinates.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

/-- Exact residual-owned coordinate schedule at one predecessor. -/
def coordinatesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Coordinate previous) :=
  capability.coordinates.read previous

/-- Framework-visible worst-case polynomial envelope. -/
def polynomialBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate} Previous}
    (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.coordinatesAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT15
