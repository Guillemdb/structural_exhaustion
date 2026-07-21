import Hypostructure.CT6.Theorems

/-!
# CT6 public automation surface

Applications provide local semantics, typed predecessor queries, a local
decider, and a polynomial envelope.  CT6 owns search, routing, generated
outputs, trace, work accounting, and the accumulated ledger extension.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

/-- Public evidence-carrying CT6 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct6Execute) "ct6_execute " term " using " term : term

macro_rules
  | `(ct6_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT6.execute _ $capability $previous)

syntax (name := ct6Verified) "ct6_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct6_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT6.run_verified _ $capability $previous)

syntax (name := ct6Total) "ct6_total " term " using " term : tactic

macro_rules
  | `(tactic| ct6_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT6.run_total _ $capability $previous)

end Hypostructure.CT6
