import Hypostructure.CT10.Search

/-!
# CT10 accumulated execution

The sealed route stores Core's direct decision and, only on its complementary
arm, Core's first-missing decision.  CT10 then installs that route as the sole
extension of the literal predecessor ledger.  Terminals, residuals, traces,
and work are all derived from the sealed route.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}

/-- Core decision type for the first direct-class scan. -/
abbrev DirectRoute (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.classesAt previous) (spec.Direct previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.classesAt previous) (spec.Direct previous) =>
      DirectAbsent capability previous)

/-- Core decision type for the first missing-class scan. -/
abbrev MissingRoute (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.classesAt previous) (Missing capability previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.classesAt previous) (Missing capability previous) =>
      NoMissingClass capability previous)

/-- Semantic CT10 terminals. -/
inductive Terminal where
  | direct
  | promoted
  | exhaustive
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT10 flow. -/
inductive NodeId where
  | entry
  | classSchedule
  | directSearch
  | datumSchedule
  | rowObservation
  | firstMissingSearch
  | promotion
  | directTerminal
  | promotedTerminal
  | exhaustiveTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed canonical traces. -/
inductive Trace : Terminal -> Type where
  | direct : Trace .direct
  | promoted : Trace .promoted
  | exhaustive : Trace .exhaustive

namespace Trace

/-- Observable node sequence for a typed CT10 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .direct, .direct =>
      [.entry, .classSchedule, .directSearch, .directTerminal]
  | .promoted, .promoted =>
      [.entry, .classSchedule, .directSearch, .datumSchedule,
        .rowObservation, .firstMissingSearch, .promotion, .promotedTerminal]
  | .exhaustive, .exhaustive =>
      [.entry, .classSchedule, .directSearch, .datumSchedule,
        .rowObservation, .firstMissingSearch, .exhaustiveTerminal]

/-- Canonical observable trace for each semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .direct =>
      [.entry, .classSchedule, .directSearch, .directTerminal]
  | .promoted =>
      [.entry, .classSchedule, .directSearch, .datumSchedule,
        .rowObservation, .firstMissingSearch, .promotion, .promotedTerminal]
  | .exhaustive =>
      [.entry, .classSchedule, .directSearch, .datumSchedule,
        .rowObservation, .firstMissingSearch, .exhaustiveTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .direct, .direct => rfl
  | .promoted, .promoted => rfl
  | .exhaustive, .exhaustive => rfl

end Trace

/-- Framework-generated promoted residual. -/
structure PromotedResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  directAbsent : DirectAbsent capability previous
  missing : MissingDatum capability previous
  promotion : spec.Promotion previous
  exact : promotion = spec.promote previous missing.value

/-- Framework-generated exhaustive finite classification certificate. -/
structure ExhaustiveCertificate (capability : Capability spec)
    (previous : Previous) : Prop where
  private mk ::
  directAbsent : DirectAbsent capability previous
  noMissing : NoMissingClass capability previous

/-- Internal terminal-indexed evidence.  The declaration is private as well as
the public route constructor, so applications cannot author an outcome. -/
private inductive RouteData (capability : Capability spec)
    (previous : Previous) : Terminal ->
    Type (max uDatum uClass uPromotion) where
  | direct (decision : DirectRoute capability previous)
      (residual : DirectResidual capability previous) :
      RouteData capability previous .direct
  | promoted (direct : DirectRoute capability previous)
      (missing : MissingRoute capability previous)
      (residual : PromotedResidual capability previous) :
      RouteData capability previous .promoted
  | exhaustive (direct : DirectRoute capability previous)
      (missing : MissingRoute capability previous)
      (certificate : ExhaustiveCertificate capability previous) :
      RouteData capability previous .exhaustive

/-- Sealed framework route.  Its constructor and terminal-indexed evidence are
inaccessible to callers. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  private data : RouteData capability previous terminal

/-- Run the two Core searches in the prescribed order. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous := by
  let direct := routeDirect capability previous
  cases directBranch : direct.added with
  | yesBranch hasDirect =>
      exact .mk .direct (.direct direct
        (direct.previous.hitOfHasHit hasDirect))
  | noBranch directAbsent =>
      let missing := routeMissing capability previous
      cases missingBranch : missing.added with
      | yesBranch hasMissing =>
          let firstMissing := missing.previous.hitOfHasHit hasMissing
          let residual : PromotedResidual capability previous :=
            .mk directAbsent firstMissing
              (spec.promote previous firstMissing.value) rfl
          exact .mk .promoted (.promoted direct missing residual)
      | noBranch noMissing =>
          exact .mk .exhaustive (.exhaustive direct missing
            (.mk directAbsent noMissing))

namespace Routed

/-- Exact primitive checks performed by the routed execution. -/
def checks {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Nat := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision _residual =>
      exact directChecks capability previous
  | promoted _direct _missing _residual =>
      exact directChecks capability previous +
        missingRowChecks capability previous
  | exhaustive _direct _missing _certificate =>
      exact directChecks capability previous +
        missingRowChecks capability previous

/-- Every routed execution lies below the complete residual-owned schedule. -/
theorem checks_le_localBound {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous) :
    routed.checks <=
      localCheckBound spec capability.data capability.classes previous := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision _residual =>
      exact (directChecks_le_classes capability previous).trans
        (Nat.le_add_right _ _)
  | promoted _direct _missing _residual =>
      exact Nat.add_le_add
        (directChecks_le_classes capability previous)
        (missingRowChecks_le_product capability previous)
  | exhaustive _direct _missing _certificate =>
      exact Nat.add_le_add
        (directChecks_le_classes capability previous)
        (missingRowChecks_le_product capability previous)

/-- Recover the first direct class only from the exact direct terminal. -/
def directResidual {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isDirect : routed.terminal = .direct) :
    DirectResidual capability previous := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision residual => exact residual
  | promoted _direct _missing _residual => cases isDirect
  | exhaustive _direct _missing _certificate => cases isDirect

/-- Recover the first missing class and computed promotion only from the exact
promoted terminal. -/
def promotedResidual {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isPromoted : routed.terminal = .promoted) :
    PromotedResidual capability previous := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision _residual => cases isPromoted
  | promoted _direct _missing residual => exact residual
  | exhaustive _direct _missing _certificate => cases isPromoted

/-- Recover complete-table evidence only from the exhaustive terminal. -/
def exhaustiveCertificate {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isExhaustive : routed.terminal = .exhaustive) :
    ExhaustiveCertificate capability previous := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision _residual => cases isExhaustive
  | promoted _direct _missing _residual => cases isExhaustive
  | exhaustive _direct _missing certificate => exact certificate

/-- Unique typed trace selected by the sealed route. -/
def trace {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal := by
  rcases routed with ⟨terminal, data⟩
  cases data with
  | direct _decision _residual => exact .direct
  | promoted _direct _missing _residual => exact .promoted
  | exhaustive _direct _missing _certificate => exact .exhaustive

end Routed

/-- Accumulated CT10 stage: the exact predecessor plus one sealed route. -/
abbrev Stage (spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed result of the canonical CT10 executor. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = stage.added.checks

namespace ExecutionResult

/-- Terminal derived from the retained route. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Exact observable trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Every execution satisfies the declared polynomial work bound. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree := by
  rw [result.checks_eq]
  exact (result.stage.added.checks_le_localBound).trans
    (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT10 on one literal predecessor ledger. -/
def run (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := routed.trace
    checks := routed.checks
    checks_eq := rfl
  }

@[simp] theorem run_previous (capability : Capability spec)
    (previous : Previous) :
    (run capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT10
