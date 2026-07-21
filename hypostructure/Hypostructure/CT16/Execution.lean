import Hypostructure.CT16.Search

/-!
# CT16 accumulated execution

The complete generated payload is appended once to the literal predecessor.
Its constructor is private, so applications cannot choose a terminal, trace,
outcome, or work count.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Semantic CT16 terminals. -/
inductive Terminal where
  | properSupport
  | exactCode
  | mismatch
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT16 reference trace. -/
inductive NodeId where
  | entry
  | coordinateSchedule
  | supportScan
  | closedCodeComputation
  | codeEqualityDecision
  | properSupportTerminal
  | exactCodeTerminal
  | mismatchTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed reference traces. -/
inductive Trace : Terminal -> Type where
  | properSupport : Trace .properSupport
  | exactCode : Trace .exactCode
  | mismatch : Trace .mismatch

namespace Trace

/-- Observable nodes of a typed CT16 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .properSupport, .properSupport =>
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal]
  | .exactCode, .exactCode =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal]
  | .mismatch, .mismatch =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .properSupport =>
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal]
  | .exactCode =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal]
  | .mismatch =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .properSupport, .properSupport => rfl
  | .exactCode, .exactCode => rfl
  | .mismatch, .mismatch => rfl

end Trace

/-- Typed evidence attached to each generated terminal. -/
inductive Outcome {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Terminal -> Type _
  | properSupport (residual : ProperSupportResidual capability previous) :
      Outcome capability previous .properSupport
  | exactCode (certificate : ExactCodeCertificate capability previous) :
      Outcome capability previous .exactCode
  | mismatch (residual : ClosedTypeMismatchResidual capability previous) :
      Outcome capability previous .mismatch

/-- Whole-support terminals perform one code computation and one equality
decision; the proper-support terminal stops immediately after the scan. -/
def terminalExtraChecks : Terminal -> Nat
  | .properSupport => 0
  | .exactCode => 2
  | .mismatch => 2

/-- Complete framework-generated addition to the accumulated ledger. -/
structure Generated {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  supportExecution : Core.Finite.Search.Execution
    (capability.coordinatesAt previous)
    (fun coordinate => Not (spec.InSupport previous coordinate))
  supportExecution_eq : supportExecution = supportScan spec capability previous
  terminal : Terminal
  outcome : Outcome capability previous terminal
  trace : Trace terminal
  supportChecks : Nat
  supportChecks_eq : supportChecks =
    Core.Finite.Accounting.executionChecks supportExecution
  checks : Nat
  checks_eq : checks = supportChecks + terminalExtraChecks terminal

/-- Execute all internal CT16 computations without changing the predecessor. -/
private def generate {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Generated spec capability previous :=
  let routed := routeSupport spec capability previous
  match routed.added with
  | .yesBranch hasMissing =>
      let missing := routed.previous.hitOfHasHit hasMissing
      {
        supportExecution := routed.previous
        supportExecution_eq := rfl
        terminal := .properSupport
        outcome := .properSupport missing
        trace := .properSupport
        supportChecks := supportChecks spec capability previous
        supportChecks_eq := rfl
        checks := supportChecks spec capability previous
        checks_eq := rfl
      }
  | .noBranch whole =>
      let state := computeClosedCode capability previous whole
      let codeRoute := routeCode capability previous state
      match codeRoute.added with
      | .yesBranch equal =>
          {
            supportExecution := routed.previous
            supportExecution_eq := rfl
            terminal := .exactCode
            outcome := .exactCode
              (ExactCodeCertificate.ofEquality codeRoute.previous equal)
            trace := .exactCode
            supportChecks := supportChecks spec capability previous
            supportChecks_eq := rfl
            checks := supportChecks spec capability previous + 2
            checks_eq := rfl
          }
      | .noBranch notEqual =>
          {
            supportExecution := routed.previous
            supportExecution_eq := rfl
            terminal := .mismatch
            outcome := .mismatch
              (ClosedTypeMismatchResidual.ofInequality
                codeRoute.previous notEqual)
            trace := .mismatch
            supportChecks := supportChecks spec capability previous
            supportChecks_eq := rfl
            checks := supportChecks spec capability previous + 2
            checks_eq := rfl
          }

/-- CT16's sole accumulated-ledger extension. -/
abbrev Stage {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Generated spec capability previous

/-- Closed result with private construction. -/
structure ExecutionResult {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability

namespace ExecutionResult

/-- Framework-derived terminal. -/
def terminal {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Typed terminal evidence generated by the runner. -/
def outcome {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Exact observable trace. -/
def traceNodes {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.stage.added.trace.nodes

/-- Exact support-scan check count. -/
def supportChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.supportChecks

/-- Exact total primitive-check count. -/
def checks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.checks

/-- Support scanning never exceeds the exact incoming coordinate count. -/
theorem supportChecks_le_card {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.supportChecks ≤
      (capability.coordinatesAt result.stage.previous).card := by
  rw [supportChecks, result.stage.added.supportChecks_eq]
  rw [result.stage.added.supportExecution_eq]
  exact _root_.Hypostructure.CT16.supportChecks_le_card
    spec capability result.stage.previous

/-- Exact total count is support work plus the terminal-specific suffix. -/
theorem checks_eq {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = result.supportChecks +
      terminalExtraChecks result.terminal :=
  result.stage.added.checks_eq

/-- Every execution is bounded by one full support scan and two operations. -/
theorem checks_le_worstCase {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ capability.worstCaseChecks result.stage.previous := by
  rw [result.checks_eq]
  change result.supportChecks + terminalExtraChecks result.terminal ≤
    (capability.coordinatesAt result.stage.previous).card + 2
  have supportBound := result.supportChecks_le_card
  exact Nat.add_le_add supportBound (by
    cases result.terminal <;> simp [terminalExtraChecks])

/-- Every generated execution satisfies CT16's linear work envelope. -/
theorem checks_le_polynomial {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ (capability.linearWorkBudget).coefficient *
      ((capability.linearWorkBudget).size result.stage.previous + 1) ^
        (capability.linearWorkBudget).degree :=
  result.checks_le_worstCase.trans
    (capability.linearWorkBudget.bounded result.stage.previous)

end ExecutionResult

/-- Execute CT16 on one literal predecessor and append one generated payload. -/
def run {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  .mk (Core.Residual.Ledger.extend previous
    (generate spec capability previous))

@[simp] theorem run_previous {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT16
