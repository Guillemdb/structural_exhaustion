import Hypostructure.CT12.ListPeeling

/-!
# CT12 public automation surface

Applications provide only the local indexed peeling semantics and typed
predecessor query.  CT12 owns restoration selection, recursion, routing,
generated outputs, exact trace, work accounting, and ledger extension.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

/-- Public evidence-carrying CT12 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct12Execute) "ct12_execute " term " using " term : term

macro_rules
  | `(ct12_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT12.execute _ $capability $previous)

syntax (name := ct12Verified) "ct12_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct12_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT12.run_verified _ $capability $previous)

syntax (name := ct12Total) "ct12_total " term " using " term : tactic

macro_rules
  | `(tactic| ct12_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT12.run_total _ $capability $previous)

end Hypostructure.CT12
