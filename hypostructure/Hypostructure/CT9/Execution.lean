import Hypostructure.CT9.Search

/-!
# CT9 accumulated execution

The deterministic reference machine computes the exact partition and lets
Core route the first-overload decision.  A completed execution contributes
one private routed extension to its literal predecessor and no other state.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}

/-- Exhaustive CT9 terminals. -/
inductive Terminal where
  | overloaded
  | bounded
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT9 flow. -/
inductive NodeId where
  | entry
  | itemSchedule
  | labelSchedule
  | partition
  | overloadSearch
  | overloadedTerminal
  | boundedTerminal
  deriving DecidableEq, Repr

/-- Framework-generated terminal evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | overloaded (partition : Partition capability previous)
      (residual : OverloadResidual capability previous partition) :
      Outcome capability previous .overloaded
  | bounded (certificate : BoundedCertificate capability previous) :
      Outcome capability previous .bounded

/-- Terminal-indexed exact CT9 trace. -/
inductive Trace : Terminal -> Type where
  | overloaded : Trace .overloaded
  | bounded : Trace .bounded

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .overloaded, .overloaded =>
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .overloadedTerminal]
  | .bounded, .bounded =>
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .boundedTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .overloaded =>
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .overloadedTerminal]
  | .bounded =>
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .boundedTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .overloaded, .overloaded => rfl
  | .bounded, .bounded => rfl

end Trace

/-- Private framework route selected by the deterministic machine. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Execute the exact partition and Core-owned overload decision. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let partition := computePartition capability previous
  let routed := routeOverload capability previous partition
  match routed.added with
  | .yesBranch hasOverload =>
      .mk .overloaded (.overloaded partition
        (routed.previous.hitOfHasHit hasOverload))
  | .noBranch avoids =>
      .mk .bounded (.bounded
        (boundedCertificateOfAvoids capability previous partition avoids))

/-- Unique trace generated from terminal-indexed evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | overloaded _partition _residual => exact .overloaded
  | bounded _certificate => exact .bounded

/-- Unique trace generated from a private routed value. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive work of each branch.  Every inspected label pays one
complete item scan plus one capacity comparison. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .overloaded, .overloaded _partition residual =>
      (residual.index.1 + 1) * ((capability.itemsAt previous).card + 1)
  | .bounded, .bounded _certificate =>
      (capability.labelScheduleAt previous).card *
        ((capability.itemsAt previous).card + 1)

/-- Branch-exact work is bounded by the complete label-by-item schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <= localCheckBound
      (capability.itemsAt previous) (capability.labelScheduleAt previous) := by
  cases outcome with
  | overloaded partition residual =>
      unfold outcomeChecks localCheckBound
      exact Nat.mul_le_mul_right _
        (Nat.succ_le_iff.mpr residual.index.isLt)
  | bounded certificate =>
      rfl

/-- One accumulated CT9 stage: the literal predecessor plus one private
routed output. -/
abbrev Stage (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public CT9 execution. -/
structure ExecutionResult (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from retained routed evidence. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Terminal-indexed evidence retained in the single extension. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Actual branch work is bounded by the complete prescribed schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= localCheckBound
      (capability.itemsAt result.stage.previous)
      (capability.labelScheduleAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's polynomial envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT9 on one literal incoming accumulated ledger. -/
def run (spec : Spec.{uPrevious, uItem, uLabel} Previous)
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
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT9
