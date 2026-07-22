import Hypostructure.Core.Execution

/-!
# Core contracts

Domain-independent proof programs should register primitive bounds and facts in
one contract object, then let Graph, PDE, CT, and route executors consume those
contracts.  This module contains only the generic contract shapes; it has no
graph, PDE, or tactic-specific imports.
-/

namespace Hypostructure.Core.Contract

universe uStage

/-- A polynomial work envelope over a residual stage.  Applications may choose
a deliberately coarse envelope, but executors should consume it through this
Core-owned shape instead of receiving detached numeric constants. -/
structure WorkEnvelope (Stage : Sort uStage) where
  size : Stage -> Nat
  checks : Stage -> Nat
  coefficient : Nat
  degree : Nat
  bounded :
    forall stage, checks stage <= coefficient * (size stage + 1) ^ degree

/-- Convert a contract envelope to the existing executable budget shape. -/
def WorkEnvelope.toBudget {Stage : Sort uStage}
    (envelope : WorkEnvelope Stage) : PolynomialCheckBudget Stage where
  size := envelope.size
  checks := envelope.checks
  coefficient := envelope.coefficient
  degree := envelope.degree
  bounded := envelope.bounded

@[simp] theorem WorkEnvelope.toBudget_checks {Stage : Sort uStage}
    (envelope : WorkEnvelope Stage) (stage : Stage) :
    envelope.toBudget.checks stage = envelope.checks stage :=
  rfl

@[simp] theorem WorkEnvelope.toBudget_coefficient {Stage : Sort uStage}
    (envelope : WorkEnvelope Stage) :
    envelope.toBudget.coefficient = envelope.coefficient :=
  rfl

@[simp] theorem WorkEnvelope.toBudget_degree {Stage : Sort uStage}
    (envelope : WorkEnvelope Stage) :
    envelope.toBudget.degree = envelope.degree :=
  rfl

end Hypostructure.Core.Contract
