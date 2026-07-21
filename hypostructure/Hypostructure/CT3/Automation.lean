import Hypostructure.CT3.Theorems

/-!
# CT3 public automation surface

Applications provide semantic operations, typed ledger queries, local
deciders, coverage theorems, and the literal predecessor.  CT3 owns every
scan, route, output, trace, ledger extension, and work certificate.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

/-- Public evidence-carrying CT3 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct3Execute) "ct3_execute " term " using " term : term

macro_rules
  | `(ct3_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT3.execute _ $capability $previous)

syntax (name := ct3Verified) "ct3_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct3_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT3.run_verified _ $capability $previous)

syntax (name := ct3Total) "ct3_total " term " using " term : tactic

macro_rules
  | `(tactic| ct3_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT3.run_total _ $capability $previous)

end Hypostructure.CT3
