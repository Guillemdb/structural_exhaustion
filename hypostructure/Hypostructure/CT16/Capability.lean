import Hypostructure.CT16.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Query

/-!
# CT16 executable capability

The coordinate schedule is a typed read from the exact predecessor ledger.
Applications provide primitive support decisions, one counted implementation
of the specified closed code, and one counted equality decision against the
specified target code.  Both executable code operations carry exact
predecessor-indexed polynomial budgets.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Counted implementation of the mathematical closed-code denotation.

`Spec.closedCode` remains the semantic reference value.  The executable runner
uses only `run`; `correct` identifies its output with that reference, while
`checks_eq` makes the supplied polynomial budget exact rather than merely an
upper bound. -/
structure ClosedCodeComputation {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous) where
  run : (previous : Previous) -> Core.Counted (spec.ClosedCode previous)
  correct : forall previous, (run previous).value = spec.closedCode previous
  budget : Core.PolynomialCheckBudget Previous
  checks_eq : forall previous, (run previous).checks = budget.checks previous

/-- Counted literal comparison of one computed code with the registered target.

The decision itself is proof carrying, so a caller cannot supply an incorrect
branch.  Its exact cost may depend on the predecessor, but not on which branch
the comparison selects. -/
structure CodeEqualityDecision {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous) where
  run : (previous : Previous) -> (code : spec.ClosedCode previous) ->
    Core.Counted (Decidable (code = spec.targetCode previous))
  budget : Core.PolynomialCheckBudget Previous
  checks_eq : forall previous code,
    (run previous code).checks = budget.checks previous

namespace CodeEqualityDecision

/-- Register decidable equality as one explicit primitive comparison.

This constructor is appropriate only when one call to the supplied decider is
the intended primitive-check unit.  More expensive comparison procedures must
use `CodeEqualityDecision.mk` with their actual counted implementation. -/
def unitCost {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (size : Previous -> Nat)
    (decEq : (previous : Previous) -> DecidableEq (spec.ClosedCode previous)) :
    CodeEqualityDecision spec where
  run := fun previous code =>
    ⟨decEq previous code (spec.targetCode previous), 1⟩
  budget := Core.PolynomialCheckBudget.constant size 1
  checks_eq := by intros; rfl

end CodeEqualityDecision

/-- Minimal executable surface for whole-support closed-code exhaustion.

No support result, code value, equality verdict, terminal, trace, or route is
accepted from an application. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous) where
  coordinates : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Coordinate previous)
  inSupportDecidable : (previous : Previous) ->
    (coordinate : spec.Coordinate previous) ->
      Decidable (spec.InSupport previous coordinate)
  codeComputation : ClosedCodeComputation spec
  equalityDecision : CodeEqualityDecision spec

namespace Capability

/-- Exact residual-owned coordinate schedule at one predecessor. -/
def coordinatesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Coordinate previous) :=
  capability.coordinates.read previous

/-- Full support-scan budget.  An early support failure may execute a strict
prefix, but no support branch can exceed this predecessor-owned schedule. -/
def supportWorstCaseBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) : Core.PolynomialCheckBudget Previous where
  size := fun previous => (capability.coordinatesAt previous).card
  checks := fun previous => (capability.coordinatesAt previous).card
  coefficient := 1
  degree := 1
  bounded := by
    intro previous
    simp

/-- Exact complete-schedule composition: full support scan, one closed-code
computation, and one target-code equality decision. -/
def completeWorkBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) : Core.PolynomialCheckBudget Previous :=
  capability.supportWorstCaseBudget.add
    (capability.codeComputation.budget.add
      capability.equalityDecision.budget)

/-- Complete-schedule check count.  This remains a source-compatible upper
bound for callers that previously consumed `worstCaseChecks`, but now includes
the actual registered code-computation and equality costs. -/
def worstCaseChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Nat :=
  capability.completeWorkBudget.checks previous

@[simp] theorem completeWorkBudget_checks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :
    capability.completeWorkBudget.checks previous =
      (capability.coordinatesAt previous).card +
        (capability.codeComputation.budget.checks previous +
          capability.equalityDecision.budget.checks previous) :=
  rfl

@[simp] theorem worstCaseChecks_eq {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :
    capability.worstCaseChecks previous =
      (capability.coordinatesAt previous).card +
        (capability.codeComputation.budget.checks previous +
          capability.equalityDecision.budget.checks previous) :=
  rfl

/-- Historical compatibility name.  The resulting budget is polynomial but
need not be linear when the registered closed-code computation is not linear. -/
abbrev linearWorkBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) : Core.PolynomialCheckBudget Previous :=
  capability.completeWorkBudget

end Capability

end Hypostructure.CT16
