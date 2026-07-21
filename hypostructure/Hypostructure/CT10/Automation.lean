import Hypostructure.CT10.Theorems

/-!
# CT10 public automation surface

Applications provide a semantic specification, executable capability, and one
literal predecessor.  The framework owns both searches, routing, promotion,
ledger extension, traces, terminals, and exact work accounting.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

/-- Public evidence-carrying CT10 executor. -/
def execute {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run capability previous

syntax (name := ct10Execute) "ct10_execute " term " using " term : term

macro_rules
  | `(ct10_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT10.execute $capability $previous)

syntax (name := ct10Verified) "ct10_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct10_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT10.run_verified $capability $previous)

syntax (name := ct10Total) "ct10_total " term " using " term : tactic

macro_rules
  | `(tactic| ct10_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT10.run_total $capability $previous)

end Hypostructure.CT10
