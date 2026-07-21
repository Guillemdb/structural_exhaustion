import Hypostructure.CT7.Search

/-!
# CT7 accumulated execution

Core finite-search decisions choose every branch.  CT7 appends exactly one
private generated payload to the literal predecessor; callers cannot select a
terminal, outcome, trace, or work count.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Exhaustive CT7 terminals. -/
inductive Terminal where
  | realization
  | distinguishing
  | neutral
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT7 reference flow. -/
inductive NodeId where
  | entry
  | contextSchedule
  | realizationSearch
  | distinctionSearch
  | realizationTerminal
  | distinguishingTerminal
  | neutralTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed framework evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | realization (certificate : RealizationCertificate capability previous) :
      Outcome capability previous .realization
  | distinguishing
      (residual : DistinguishingResidual capability previous) :
      Outcome capability previous .distinguishing
  | neutral (certificate : NeutralityCertificate capability previous) :
      Outcome capability previous .neutral

/-- Terminal-indexed reference traces. -/
inductive Trace : Terminal -> Type where
  | realization : Trace .realization
  | distinguishing : Trace .distinguishing
  | neutral : Trace .neutral

namespace Trace

/-- Observable nodes of a typed CT7 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .realization, .realization =>
      [.entry, .contextSchedule, .realizationSearch, .realizationTerminal]
  | .distinguishing, .distinguishing =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .distinguishingTerminal]
  | .neutral, .neutral =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .neutralTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .realization =>
      [.entry, .contextSchedule, .realizationSearch, .realizationTerminal]
  | .distinguishing =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .distinguishingTerminal]
  | .neutral =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .neutralTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .realization, .realization => rfl
  | .distinguishing, .distinguishing => rfl
  | .neutral, .neutral => rfl

end Trace

/-- Routed evidence whose constructor is unavailable to applications. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Core owns both decisions and their ordered control flow. -/
private def routeReference (capability : Capability spec)
    (previous : Previous) : Routed capability previous :=
  let realization := routeRealization capability previous
  match realization.added with
  | .yesBranch hasRealization =>
      .mk .realization (.realization
        (realization.previous.hitOfHasHit hasRealization))
  | .noBranch unrealized =>
      let distinction := routeDistinction capability previous
      match distinction.added with
      | .yesBranch hasDistinction =>
          .mk .distinguishing (.distinguishing
            (DistinguishingResidual.ofHit unrealized
              (distinction.previous.hitOfHasHit hasDistinction)))
      | .noBranch neutral =>
          .mk .neutral (.neutral
            (NeutralityCertificate.ofAvoidance unrealized neutral))

/-- Unique typed trace selected from generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | realization _ => exact .realization
  | distinguishing _ => exact .distinguishing
  | neutral _ => exact .neutral

/-- Exact primitive checks charged by each generated path. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .realization, .realization certificate => certificate.index.1 + 1
  | .distinguishing, .distinguishing residual =>
      (capability.contextsAt previous).card +
        (residual.distinction.index.1 + 1)
  | .neutral, .neutral _ =>
      localCheckBound (capability.contextsAt previous)

/-- Exact charged work is bounded by the two complete residual-owned passes. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome ≤ localCheckBound
      (capability.contextsAt previous) := by
  cases outcome with
  | realization certificate =>
      have inspected : certificate.index.1 + 1 ≤
          (capability.contextsAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | distinguishing residual =>
      have inspected : residual.distinction.index.1 + 1 ≤
          (capability.contextsAt previous).card :=
        Nat.succ_le_iff.mpr residual.distinction.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | neutral _ =>
      rfl

/-- The one accumulated CT7 stage. -/
abbrev Stage
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed CT7 execution result. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Framework-derived terminal. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Typed semantic evidence retained in the generated ledger entry. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Exact observable trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Exact charged work for the generated terminal. -/
theorem checks_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = outcomeChecks result.outcome :=
  result.checks_eq

/-- Every generated path is bounded by two complete passes. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ localCheckBound
      (capability.contextsAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every generated execution satisfies CT7's automatic linear envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ (capability.linearWorkBudget).coefficient *
      ((capability.linearWorkBudget).size result.stage.previous + 1) ^
        (capability.linearWorkBudget).degree :=
  result.checks_le_limit.trans
    (capability.linearWorkBudget.bounded result.stage.previous)

end ExecutionResult

/-- Execute CT7 on one literal predecessor and append one generated payload. -/
def run
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  .mk (Core.Residual.Ledger.extend previous routed)
    (traceOfOutcome routed.outcome) (outcomeChecks routed.outcome) rfl

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT7
