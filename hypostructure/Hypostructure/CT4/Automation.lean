import Hypostructure.CT4.Cardinality

/-!
# CT4 public automation surface

Applications provide domain-neutral charging semantics, typed schedule
queries, primitive eligibility decisions, and one literal predecessor.  CT4
owns assignment, all scans, all routing, the generated ledger extension,
trace, and work proof.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

/-- Public evidence-carrying CT4 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uDemand, uPayer} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct4Execute) "ct4_execute " term " using " term : term

macro_rules
  | `(ct4_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT4.execute _ $capability $previous)

syntax (name := ct4Verified) "ct4_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct4_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT4.run_verified _ $capability $previous)

syntax (name := ct4Total) "ct4_total " term " using " term : tactic

macro_rules
  | `(tactic| ct4_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT4.run_total _ $capability $previous)

end Hypostructure.CT4
