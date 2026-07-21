import Hypostructure.CT1.Search

/-!
# CT1 accumulated execution

Execution stores the Core-routed scan as one dependent extension of the
literal incoming ledger.  Terminal tags and traces are computed from that
route, never supplied by an application.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Semantic CT1 terminals. -/
inductive Terminal where
  | c1
  | avoiding
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT1 reference trace. -/
inductive NodeId where
  | entry
  | schedule
  | realizationDecision
  | c1Terminal
  | avoidingTerminal
  deriving DecidableEq, Repr

/-- A terminal-indexed trace.  Ill-typed terminal traces cannot be stored. -/
inductive Trace : Terminal -> Type where
  | c1 : Trace .c1
  | avoiding : Trace .avoiding

namespace Trace

/-- Observable node sequence of a typed CT1 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .c1, .c1 => [.entry, .schedule, .realizationDecision, .c1Terminal]
  | .avoiding, .avoiding =>
      [.entry, .schedule, .realizationDecision, .avoidingTerminal]

/-- Reference node sequence associated with a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .c1 => [.entry, .schedule, .realizationDecision, .c1Terminal]
  | .avoiding =>
      [.entry, .schedule, .realizationDecision, .avoidingTerminal]

/-- The terminal index fixes the complete observable trace. -/
theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .c1, .c1 => rfl
  | .avoiding, .avoiding => rfl

end Trace

/-- The Core route determines the semantic terminal. -/
def terminalOfRoute {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (routed : RoutedSearch spec capability previous) : Terminal :=
  match routed.added with
  | .yesBranch _ => .c1
  | .noBranch _ => .avoiding

/-- Construct the unique typed trace selected by the Core route. -/
def traceOfRoute {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (routed : RoutedSearch spec capability previous) :
    Trace (terminalOfRoute routed) := by
  cases branch : routed.added with
  | yesBranch _ =>
      simpa [terminalOfRoute, branch] using Trace.c1
  | noBranch _ =>
      simpa [terminalOfRoute, branch] using Trace.avoiding

/-- Accumulated CT1 stage.  Its `previous` field is the complete literal input
ledger and its sole addition is the framework-routed finite scan. -/
abbrev Stage {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    RoutedSearch spec capability previous

/-- Closed result of the canonical CT1 executor.  The private constructor
prevents applications from pairing an arbitrary terminal with a ledger. -/
structure ExecutionResult {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace (terminalOfRoute stage.added)
  checks : Nat
  checks_eq : checks =
    Core.Finite.Accounting.executionChecks stage.added.previous

namespace ExecutionResult

/-- Terminal derived from the stored Core route. -/
def terminal {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  terminalOfRoute result.stage.added

/-- Observable exact trace. -/
def traceNodes {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Every visible check count is bounded by the exact incoming schedule. -/
theorem checks_le_schedule {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      searchCheckBound spec capability.schedule result.stage.previous := by
  rw [result.checks_eq]
  exact Core.Finite.Accounting.executionChecks_le_card
    result.stage.added.previous

/-- Every execution satisfies the declared polynomial work bound. -/
theorem checks_le_polynomial {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_schedule.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT1 on one literal incoming ledger. -/
def run {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := route spec capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRoute routed
    checks := Core.Finite.Accounting.executionChecks routed.previous
    checks_eq := rfl
  }

@[simp] theorem run_previous {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT1
