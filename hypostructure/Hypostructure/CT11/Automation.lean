import Hypostructure.CT11.NegativeBudget

/-!
# CT11 public automation surface

Applications provide primitive local semantics and typed predecessor queries.
CT11 owns both searches, decisions, generated residuals, trace, accounting,
and the sole accumulated-ledger extension.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

/-- Public evidence-carrying CT11 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct11Execute) "ct11_execute " term " using " term : term

macro_rules
  | `(ct11_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT11.execute _ $capability $previous)

syntax (name := ct11Verified) "ct11_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct11_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT11.run_verified _ $capability $previous)

syntax (name := ct11Total) "ct11_total " term " using " term : tactic

macro_rules
  | `(tactic| ct11_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT11.run_total _ $capability $previous)

end Hypostructure.CT11
