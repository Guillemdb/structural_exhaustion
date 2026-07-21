import Hypostructure.CT5.Theorems

/-!
# CT5 public automation surface

Applications provide one literal predecessor and a capability.  CT5 owns all
finite scans, resource comparisons, traces, outcomes, and ledger extension.
-/

namespace Hypostructure.CT5

universe uPrevious uSite uWitness uResource

/-- Public evidence-carrying CT5 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct5Execute) "ct5_execute " term " using " term : term

macro_rules
  | `(ct5_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT5.execute _ $capability $previous)

syntax (name := ct5Verified) "ct5_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct5_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT5.run_verified _ $capability $previous)

syntax (name := ct5Total) "ct5_total " term " using " term : tactic

macro_rules
  | `(tactic| ct5_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT5.run_total _ $capability $previous)

end Hypostructure.CT5
