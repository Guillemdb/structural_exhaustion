import Hypostructure.CT6.Search

/-!
# CT6 accumulated execution

The deterministic reference machine lets Core choose the search branch, then
stores one private routed value in one extension of the literal predecessor.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uIndex, uData} Previous}

/-- The two exhaustive CT6 terminals. -/
inductive Terminal where
  | firstFailure
  | activeLedger
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT6 pass. -/
inductive NodeId where
  | entry
  | failureOrder
  | activityScan
  | activeLedgerComputation
  | firstFailureTerminal
  | activeLedgerTerminal
  deriving DecidableEq, Repr

/-- Framework-generated evidence indexed by the selected terminal. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | firstFailure (residual : FirstFailureResidual capability previous) :
      Outcome capability previous .firstFailure
  | activeLedger (residual : ActiveLedgerResidual capability previous) :
      Outcome capability previous .activeLedger

/-- Terminal-indexed CT6 trace. -/
inductive Trace : Terminal -> Type where
  | firstFailure : Trace .firstFailure
  | activeLedger : Trace .activeLedger

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .firstFailure, .firstFailure =>
      [.entry, .failureOrder, .activityScan, .firstFailureTerminal]
  | .activeLedger, .activeLedger =>
      [.entry, .failureOrder, .activityScan, .activeLedgerComputation,
        .activeLedgerTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .firstFailure =>
      [.entry, .failureOrder, .activityScan, .firstFailureTerminal]
  | .activeLedger =>
      [.entry, .failureOrder, .activityScan, .activeLedgerComputation,
        .activeLedgerTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .firstFailure, .firstFailure => rfl
  | .activeLedger, .activeLedger => rfl

end Trace

/-- Private route selected by the canonical Core scan and decision. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Execute the Core-owned first-hit route and compute its exact residual. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let activity := routeActivity capability previous
  match activity.added with
  | .yesBranch hasFailure =>
      .mk .firstFailure (.firstFailure
        (firstFailureOfHit capability previous
          (activity.previous.hitOfHasHit hasFailure)))
  | .noBranch noFailure =>
      .mk .activeLedger (.activeLedger
        (buildActiveLedger capability previous noFailure))

/-- Unique typed trace selected by generated branch evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | firstFailure _ => exact .firstFailure
  | activeLedger _ => exact .activeLedger

/-- Unique typed trace selected by the private routed value. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- One CT6 execution is one extension of the literal incoming ledger. -/
abbrev Stage (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public result of one ordered CT6 pass. -/
structure ExecutionResult (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_exact : checks = Core.Finite.Accounting.executionChecks
    (activityScan capability stage.previous)

namespace ExecutionResult

/-- Terminal derived from the exact routed value retained in the ledger. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Exact terminal-indexed output retained by this execution. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Exact scan work is bounded by the residual-owned order length. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= localCheckBound
      (capability.failureOrderAt result.stage.previous) := by
  rw [result.checks_exact]
  exact Core.Finite.Accounting.executionChecks_le_card
    (activityScan capability result.stage.previous)

/-- Every execution satisfies the capability's polynomial envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT6 on one literal predecessor ledger. -/
def run (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRouted routed
    checks := Core.Finite.Accounting.executionChecks
      (activityScan capability previous)
    checks_exact := rfl
  }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT6
