import Hypostructure.CT11.Search

/-!
# CT11 accumulated execution

The deterministic reference machine lets Core choose both search branches.
It stores one private routed value in one extension of the literal predecessor;
the intermediate decision stages remain internal to the executor.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCell} Previous}

/-- The two exhaustive public CT11 terminals. -/
inductive Terminal where
  | admissibilityGap
  | localizedDeficit
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT11 pass. -/
inductive NodeId where
  | entry
  | cellSchedule
  | admissibilityScan
  | negativeTotal
  | negativeBudgetScan
  | admissibilityGapTerminal
  | localizedDeficitTerminal
  deriving DecidableEq, Repr

/-- Framework-generated evidence indexed by the selected terminal. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | admissibilityGap
      (residual : AdmissibilityGapResidual capability previous) :
      Outcome capability previous .admissibilityGap
  | localizedDeficit
      (residual : LocalizedDeficitResidual capability previous) :
      Outcome capability previous .localizedDeficit

/-- Terminal-indexed CT11 trace. -/
inductive Trace : Terminal -> Type where
  | admissibilityGap : Trace .admissibilityGap
  | localizedDeficit : Trace .localizedDeficit

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .admissibilityGap, .admissibilityGap =>
      [.entry, .cellSchedule, .admissibilityScan,
        .admissibilityGapTerminal]
  | .localizedDeficit, .localizedDeficit =>
      [.entry, .cellSchedule, .admissibilityScan, .negativeTotal,
        .negativeBudgetScan, .localizedDeficitTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .admissibilityGap =>
      [.entry, .cellSchedule, .admissibilityScan,
        .admissibilityGapTerminal]
  | .localizedDeficit =>
      [.entry, .cellSchedule, .admissibilityScan, .negativeTotal,
        .negativeBudgetScan, .localizedDeficitTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .admissibilityGap, .admissibilityGap => rfl
  | .localizedDeficit, .localizedDeficit => rfl

end Trace

/-- Private framework route selected by the canonical Core scans. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Execute both Core-owned decisions and generate the exact terminal payload. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let admissibilityRoute := routeAdmissibility capability previous
  match admissibilityRoute.added with
  | .yesBranch hasGap =>
      .mk .admissibilityGap (.admissibilityGap
        (admissibilityRoute.previous.hitOfHasHit hasGap))
  | .noBranch complete =>
      let admissible :=
        buildAdmissibleDecomposition capability previous complete
      let negativeRoute := routeNegative capability previous
      match negativeRoute.added with
      | .yesBranch hasNegative =>
          .mk .localizedDeficit (.localizedDeficit
            (buildLocalizedDeficit capability previous admissible
              (negativeRoute.previous.hitOfHasHit hasNegative)))
      | .noBranch noNegative =>
          (noNegativeCell_false capability previous noNegative).elim

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | admissibilityGap _ => exact .admissibilityGap
  | localizedDeficit _ => exact .localizedDeficit

/-- Unique typed trace selected by a private routed value. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive inspections charged by each generated outcome.

The gap branch stops at its first inadmissible cell.  The localization branch
first exhausts all admissibility checks, then stops at its first negative
local budget.
-/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .admissibilityGap, .admissibilityGap residual =>
      residual.index.1 + 1
  | .localizedDeficit, .localizedDeficit residual =>
      (capability.cellsAt previous).card + residual.hit.index.1 + 1

/-- Branch-exact work is bounded by the prescribed two complete scans. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <= localCheckBound (capability.cellsAt previous) := by
  cases outcome with
  | admissibilityGap residual =>
      have inspected : residual.index.1 + 1 <=
          (capability.cellsAt previous).card :=
        Nat.succ_le_iff.mpr residual.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | localizedDeficit residual =>
      have inspected : residual.hit.index.1 + 1 <=
          (capability.cellsAt previous).card :=
        Nat.succ_le_iff.mpr residual.hit.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega

/-- One CT11 execution is one extension of the literal incoming ledger. -/
abbrev Stage (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public result of one CT11 pass. -/
structure ExecutionResult (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_exact : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from the private route retained in the ledger. -/
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

/-- Actual branch work is bounded by the complete CT11 schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.cellsAt result.stage.previous) := by
  rw [result.checks_exact]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's polynomial work envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT11 on one literal predecessor ledger. -/
def run (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRouted routed
    checks := outcomeChecks routed.outcome
    checks_exact := rfl
  }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT11
