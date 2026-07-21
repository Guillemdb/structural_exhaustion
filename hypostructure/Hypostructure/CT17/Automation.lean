import Hypostructure.CT17.Theorems

/-!
# CT17 public automation surface

Callers pass one literal predecessor and a capability assembled from typed
ledger queries.  CT17 owns all generated data and routing.
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

/-- Public evidence-carrying CT17 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct17Execute) "ct17_execute " term " using " term : term

macro_rules
  | `(ct17_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT17.execute _ $capability $previous)

syntax (name := ct17Verified) "ct17_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct17_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT17.run_verified _ $capability $previous)

syntax (name := ct17Total) "ct17_total " term " using " term : tactic

macro_rules
  | `(tactic| ct17_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT17.run_total _ $capability $previous)

end Hypostructure.CT17
