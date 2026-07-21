import Hypostructure.CT15.Theorems

/-!
# CT15 public automation surface

Applications provide primitive semantics, typed ledger queries, decisions,
and the literal predecessor.  CT15 owns rank computation, both routes, all
outputs, tracing, accounting, and ledger extension.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

/-- Public evidence-carrying CT15 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct15Execute) "ct15_execute " term " using " term : term

macro_rules
  | `(ct15_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT15.execute _ $capability $previous)

syntax (name := ct15Verified) "ct15_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct15_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT15.run_verified _ $capability $previous)

syntax (name := ct15Total) "ct15_total " term " using " term : tactic

macro_rules
  | `(tactic| ct15_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT15.run_total _ $capability $previous)

end Hypostructure.CT15
