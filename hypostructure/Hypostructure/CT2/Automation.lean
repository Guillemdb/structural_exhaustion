import Hypostructure.CT2.Theorems

/-!
# CT2 public automation surface

Applications provide primitive local-deletion semantics and the literal
predecessor.  Hypostructure owns selection, decision, routing, extension,
terminal, trace, and work accounting.

Bounded replacement is deliberately absent from this first profile.  It will
be added only when a consumer supplies residual-owned candidate and compatible
context carriers that require the more general CT2 contract.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- Public evidence-carrying CT2 executor. -/
def execute
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    ExecutionResult capability :=
  run capability previous

syntax (name := ct2Execute) "ct2_execute " term " using " term : term

macro_rules
  | `(ct2_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT2.execute $capability $previous)

syntax (name := ct2Verified) "ct2_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct2_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT2.run_verified $capability $previous)

syntax (name := ct2Total) "ct2_total " term " using " term : tactic

macro_rules
  | `(tactic| ct2_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT2.run_total $capability $previous)

end Hypostructure.CT2
