import Hypostructure.CT8.Theorems

/-!
# CT8 public automation surface

Applications supply one semantic specification, its residual-query capability,
and the literal predecessor.  CT8 owns both scans, both routes, the generated
removal, ledger extension, terminal, trace, and work account.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

/-- Public evidence-carrying CT8 executor. -/
def execute {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous}
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

syntax (name := ct8Execute) "ct8_execute " term " using " term : term

macro_rules
  | `(ct8_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT8.execute $capability $previous)

syntax (name := ct8Verified) "ct8_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct8_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT8.run_verified _ $capability $previous)

syntax (name := ct8Total) "ct8_total " term " using " term : tactic

macro_rules
  | `(tactic| ct8_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT8.run_total _ $capability $previous)

end Hypostructure.CT8
