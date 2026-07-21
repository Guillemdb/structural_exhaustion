import Hypostructure.CT13.Theorems

/-!
# CT13 public automation surface

Applications instantiate primitive semantics and residual queries, then pass
one literal predecessor.  CT13 owns all selection, routing, generated state,
trace, accounting, and ledger extension.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

/-- Public evidence-carrying CT13 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct13Execute) "ct13_execute " term " using " term : term

macro_rules
  | `(ct13_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT13.execute _ $capability $previous)

syntax (name := ct13Verified) "ct13_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct13_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT13.run_verified _ $capability $previous)

syntax (name := ct13Total) "ct13_total " term " using " term : tactic

macro_rules
  | `(tactic| ct13_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT13.run_total _ $capability $previous)

end Hypostructure.CT13
