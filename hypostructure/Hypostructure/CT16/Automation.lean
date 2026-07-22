import Hypostructure.CT16.Theorems

/-!
# CT16 public automation surface

Applications provide one capability and the literal predecessor.  CT16 owns
query evaluation, one counted support scan, one counted code computation on the
whole-support branch, one counted equality decision, the single ledger
extension, terminal evidence, tracing, and exact composed accounting.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Public evidence-carrying CT16 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct16Execute) "ct16_execute " term " using " term : term

macro_rules
  | `(ct16_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT16.execute _ $capability $previous)

syntax (name := ct16Verified) "ct16_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct16_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT16.run_verified _ $capability $previous)

syntax (name := ct16Total) "ct16_total " term " using " term : tactic

macro_rules
  | `(tactic| ct16_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT16.run_total _ $capability $previous)

end Hypostructure.CT16
