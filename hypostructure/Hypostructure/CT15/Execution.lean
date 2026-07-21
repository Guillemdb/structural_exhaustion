import Hypostructure.CT15.Search

/-!
# CT15 accumulated execution

Core finite search and Core binary decisions select every branch.  CT15 stores
the generated terminal-indexed evidence as one extension of the literal
incoming ledger.  Both the routed value and the public execution result have
private constructors.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCoordinate} Previous}

/-- Exhaustive CT15 terminals. -/
inductive Terminal where
  | rankDrop
  | c4
  | fullRankLedger
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT15 reference flow. -/
inductive NodeId where
  | entry
  | rankComputation
  | firstDropSearch
  | ledgerComputation
  | capacityComparison
  | rankDropTerminal
  | c4Terminal
  | fullRankLedgerTerminal
  deriving DecidableEq, Repr

/-- Framework-generated branch evidence, indexed by the selected terminal. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | rankDrop (rank : RankState capability previous)
      (certificate : RankDropCertificate capability previous) :
      Outcome capability previous .rankDrop
  | c4 (rank : RankState capability previous)
      (full : FullRankState capability previous rank)
      (ledger : ChargeLedger capability previous full)
      (certificate : C4Certificate capability previous ledger) :
      Outcome capability previous .c4
  | fullRankLedger (rank : RankState capability previous)
      (full : FullRankState capability previous rank)
      (ledger : ChargeLedger capability previous full)
      (residual : FullRankLedgerResidual capability previous ledger) :
      Outcome capability previous .fullRankLedger

/-- Terminal-indexed CT15 trace. -/
inductive Trace : Terminal -> Type where
  | rankDrop : Trace .rankDrop
  | c4 : Trace .c4
  | fullRankLedger : Trace .fullRankLedger

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .rankDrop, .rankDrop =>
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal]
  | .c4, .c4 =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal]
  | .fullRankLedger, .fullRankLedger =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .rankDrop =>
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal]
  | .c4 =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal]
  | .fullRankLedger =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .rankDrop, .rankDrop => rfl
  | .c4, .c4 => rfl
  | .fullRankLedger, .fullRankLedger => rfl

end Trace

/-- CT15-routed evidence.  Its private constructor prevents callers from
selecting a terminal or installing unrelated branch evidence. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Core routes first-drop and capacity decisions; CT15 retains only their
exact generated semantic evidence. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let rank := computeRank capability previous
  let dropped := routeDrop capability previous
  match dropped.added with
  | .yesBranch hasDrop =>
      .mk .rankDrop (.rankDrop rank
        (dropped.previous.hitOfHasHit hasDrop))
  | .noBranch independence =>
      let full := fullRankOfIndependence capability previous rank independence
      let ledger := buildLedger capability previous full
      let comparison := compareLedger capability previous ledger
      match comparison.added with
      | .yesBranch exceeded =>
          .mk .c4 (.c4 rank full ledger (by
            have exactExceeded := exceeded
            rw [show comparison.previous = ledger from rfl] at exactExceeded
            exact exactExceeded))
      | .noBranch available =>
          .mk .fullRankLedger
            (.fullRankLedger rank full ledger (by
              have exactAvailable := available
              rw [show comparison.previous = ledger from rfl] at exactAvailable
              exact exactAvailable))

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | rankDrop _ _ => exact .rankDrop
  | c4 _ _ _ _ => exact .c4
  | fullRankLedger _ _ _ _ => exact .fullRankLedger

/-- Unique typed trace selected by the private routed result. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive decisions charged by each terminal.

The rank pass inspects every coordinate.  A drop then pays exactly its first
hit prefix.  A full-rank outcome pays the exhaustive second pass and one
capacity comparison.  Pure charge evaluation is mathematical data
construction, not a predicate decision. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .rankDrop, .rankDrop _ certificate =>
      (capability.coordinatesAt previous).card + certificate.index.1 + 1
  | .c4, .c4 _ _ _ _ =>
      localCheckBound (capability.coordinatesAt previous)
  | .fullRankLedger, .fullRankLedger _ _ _ _ =>
      localCheckBound (capability.coordinatesAt previous)

/-- Branch-exact work never exceeds the complete prescribed schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.coordinatesAt previous) := by
  cases outcome with
  | rankDrop _ certificate =>
      have inspected : certificate.index.1 + 1 <=
          (capability.coordinatesAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | c4 _ _ _ _ => rfl
  | fullRankLedger _ _ _ _ => rfl

/-- The accumulated CT15 stage retains the literal predecessor and one
private routed framework value. -/
abbrev Stage (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed CT15 execution result. -/
structure ExecutionResult (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from retained private route evidence. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Terminal-indexed semantic output retained by the ledger extension. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Actual branch work is bounded by the complete CT15 schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.coordinatesAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's declared polynomial bound. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT15 on one literal incoming accumulated ledger. -/
def run (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRouted routed
    checks := outcomeChecks routed.outcome
    checks_eq := rfl
  }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT15
