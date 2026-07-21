import Hypostructure.CT16.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Query

/-!
# CT16 executable capability

The coordinate schedule is a typed read from the exact predecessor ledger.
Applications provide only primitive support and code-equality decisions.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Minimal executable surface for whole-support closed-code exhaustion. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous) where
  coordinates : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Coordinate previous)
  inSupportDecidable : (previous : Previous) ->
    (coordinate : spec.Coordinate previous) ->
      Decidable (spec.InSupport previous coordinate)
  codeDecidableEq : (previous : Previous) ->
    DecidableEq (spec.ClosedCode previous)

namespace Capability

/-- Exact residual-owned coordinate schedule at one predecessor. -/
def coordinatesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Coordinate previous) :=
  capability.coordinates.read previous

/-- Worst-case primitive checks: one per coordinate, one code computation,
and one literal equality decision. -/
def worstCaseChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Nat :=
  (capability.coordinatesAt previous).card + 2

/-- Framework-owned linear envelope for the complete CT16 executor. -/
def linearWorkBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) : Core.PolynomialCheckBudget Previous where
  size := fun previous => (capability.coordinatesAt previous).card
  checks := capability.worstCaseChecks
  coefficient := 2
  degree := 1
  bounded := by
    intro previous
    simp only [worstCaseChecks, Nat.pow_one]
    omega

end Capability

end Hypostructure.CT16
