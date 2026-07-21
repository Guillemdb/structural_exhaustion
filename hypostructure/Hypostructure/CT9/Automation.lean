import Hypostructure.CT9.Profiles

/-!
# CT9 public automation surface

Applications instantiate primitive semantics and pass one literal predecessor.
CT9 owns partition construction, scans, routing, traces, results, and ledger
extension.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

/-- Public evidence-carrying CT9 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

/-- Execute the derived parity-capacity-one machine. -/
def executeParityCapacityOne {Previous : Type uPrevious}
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous)
    (previous : Previous) :
    ExecutionResult profile.spec profile.capability :=
  run profile.spec profile.capability previous

syntax (name := ct9Execute) "ct9_execute " term " using " term : term

macro_rules
  | `(ct9_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT9.execute _ $capability $previous)

syntax (name := ct9Verified) "ct9_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct9_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT9.run_verified _ $capability $previous)

syntax (name := ct9Total) "ct9_total " term " using " term : tactic

macro_rules
  | `(tactic| ct9_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT9.run_total _ $capability $previous)

end Hypostructure.CT9
