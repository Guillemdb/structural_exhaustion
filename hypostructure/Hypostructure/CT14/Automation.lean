import Hypostructure.CT14.Theorems

/-!
# CT14 public automation surface

Applications instantiate primitive semantics and pass one literal predecessor.
CT14 owns every scan, ledger, decision, route, trace, result, and extension.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

/-- Public evidence-carrying CT14 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct14Execute) "ct14_execute " term " using " term : term

macro_rules
  | `(ct14_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT14.execute _ $capability $previous)

syntax (name := ct14Verified) "ct14_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct14_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT14.run_verified _ $capability $previous)

syntax (name := ct14Total) "ct14_total " term " using " term : tactic

macro_rules
  | `(tactic| ct14_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT14.run_total _ $capability $previous)

end Hypostructure.CT14
