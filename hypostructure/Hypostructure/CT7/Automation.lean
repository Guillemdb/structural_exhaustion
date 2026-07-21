import Hypostructure.CT7.Theorems

/-!
# CT7 public automation surface

Applications provide semantic operations, predecessor queries, primitive
deciders, and coverage.  CT7 owns scans, branch order, routes, generated
outputs, tracing, ledger extension, and accounting.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

/-- Public evidence-carrying CT7 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct7Execute) "ct7_execute " term " using " term : term

macro_rules
  | `(ct7_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT7.execute _ $capability $previous)

syntax (name := ct7Verified) "ct7_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct7_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT7.run_verified _ $capability $previous)

syntax (name := ct7Total) "ct7_total " term " using " term : tactic

macro_rules
  | `(tactic| ct7_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT7.run_total _ $capability $previous)

end Hypostructure.CT7
