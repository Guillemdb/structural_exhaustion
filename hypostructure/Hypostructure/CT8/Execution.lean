import Hypostructure.CT8.Search

/-!
# CT8 accumulated execution

Core selects both first-hit branches.  CT8 records one sealed routed value in
exactly one extension of the literal predecessor.  Terminal tags, traces,
certificates, removals, and work counts are generated from that route.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
    Previous}

/-- Exhaustive CT8 terminals. -/
inductive Terminal where
  | noRepetition
  | separation
  | removal
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT8 flow. -/
inductive NodeId where
  | entry
  | stateSequence
  | orderedPairSchedule
  | repeatedTypeSearch
  | responseContextSchedule
  | responseSearch
  | removalComputation
  | noRepetitionTerminal
  | separationTerminal
  | removalTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed framework evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | noRepetition
      (certificate : NoRepetitionCertificate capability previous) :
      Outcome capability previous .noRepetition
  | separation
      (residual : SeparationResidual capability previous) :
      Outcome capability previous .separation
  | removal
      (certificate : RemovalCertificate capability previous) :
      Outcome capability previous .removal

/-- Terminal-indexed canonical CT8 trace. -/
inductive Trace : Terminal -> Type where
  | noRepetition : Trace .noRepetition
  | separation : Trace .separation
  | removal : Trace .removal

namespace Trace

/-- Observable nodes of a typed CT8 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .noRepetition, .noRepetition =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .noRepetitionTerminal]
  | .separation, .separation =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .responseContextSchedule, .responseSearch, .separationTerminal]
  | .removal, .removal =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .responseContextSchedule, .responseSearch, .removalComputation,
        .removalTerminal]

/-- Canonical node sequence fixed by the semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .noRepetition =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .noRepetitionTerminal]
  | .separation =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .responseContextSchedule, .responseSearch, .separationTerminal]
  | .removal =>
      [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
        .responseContextSchedule, .responseSearch, .removalComputation,
        .removalTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .noRepetition, .noRepetition => rfl
  | .separation, .separation => rfl
  | .removal, .removal => rfl

end Trace

/-- Sealed route selected by the two Core decisions. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  private outcome : Outcome capability previous terminal

/-- Run pair discovery and, only on its repeated branch, exact response
analysis. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let repetition := routeRepetition capability previous
  match repetition.added with
  | .noBranch avoidance =>
      .mk .noRepetition (.noRepetition
        (noRepetitionOfAvoidance capability previous avoidance))
  | .yesBranch hasRepeated =>
      let pair := repetition.previous.hitOfHasHit hasRepeated
      let response := routeResponse capability previous pair
      match response.added with
      | .yesBranch hasSeparator =>
          .mk .separation (.separation
            (separationOfHit capability previous pair
              (response.previous.hitOfHasHit hasSeparator)))
      | .noBranch equalResponses =>
          .mk .removal (.removal
            (removalOfAvoidance capability previous pair equalResponses))

/-- Unique typed trace selected from generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | noRepetition _ => exact .noRepetition
  | separation _ => exact .separation
  | removal _ => exact .removal

/-- Branch-exact primitive comparison count. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .noRepetition, .noRepetition _ =>
      (capability.orderedPairsAt previous).toEnumeration.card
  | .separation, .separation residual =>
      (residual.pair.index.1 + 1) + (residual.separator.index.1 + 1)
  | .removal, .removal certificate =>
      (certificate.pair.index.1 + 1) +
        (capability.responseContextsAt previous).toEnumeration.card

/-- Every generated branch lies below the complete prescribed pair and
response schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.sequenceAt previous)
        (capability.responseContextsAt previous).toEnumeration := by
  cases outcome with
  | noRepetition _ =>
      change (capability.orderedPairsAt previous).toEnumeration.card <=
        (capability.orderedPairsAt previous).toEnumeration.card +
          (capability.responseContextsAt previous).toEnumeration.card
      exact Nat.le_add_right _ _
  | separation residual =>
      have pairInspected : residual.pair.index.1 + 1 <=
          (capability.orderedPairsAt previous).toEnumeration.card :=
        Nat.succ_le_iff.mpr residual.pair.index.isLt
      have responseInspected : residual.separator.index.1 + 1 <=
          (capability.responseContextsAt previous).toEnumeration.card :=
        Nat.succ_le_iff.mpr residual.separator.index.isLt
      change (residual.pair.index.1 + 1) +
          (residual.separator.index.1 + 1) <=
        (capability.orderedPairsAt previous).toEnumeration.card +
          (capability.responseContextsAt previous).toEnumeration.card
      exact Nat.add_le_add pairInspected responseInspected
  | removal certificate =>
      have pairInspected : certificate.pair.index.1 + 1 <=
          (capability.orderedPairsAt previous).toEnumeration.card :=
        Nat.succ_le_iff.mpr certificate.pair.index.isLt
      change (certificate.pair.index.1 + 1) +
          (capability.responseContextsAt previous).toEnumeration.card <=
        (capability.orderedPairsAt previous).toEnumeration.card +
          (capability.responseContextsAt previous).toEnumeration.card
      exact Nat.add_le_add_right pairInspected _

namespace Routed

/-- Generated typed outcome retained by a sealed route. -/
def generatedOutcome {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) :
    Outcome capability previous routed.terminal :=
  routed.outcome

/-- Exact checks selected by the generated route. -/
def checks {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Nat :=
  outcomeChecks routed.outcome

/-- Unique trace selected by the generated route. -/
def trace {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Recover no-repetition evidence only from that exact terminal. -/
def noRepetitionCertificate {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isNoRepetition : routed.terminal = .noRepetition) :
    NoRepetitionCertificate capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | noRepetition certificate => exact certificate
  | separation _ => cases isNoRepetition
  | removal _ => cases isNoRepetition

/-- Recover separation evidence only from that exact terminal. -/
def separationResidual {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isSeparation : routed.terminal = .separation) :
    SeparationResidual capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | noRepetition _ => cases isSeparation
  | separation residual => exact residual
  | removal _ => cases isSeparation

/-- Recover strict-removal evidence only from that exact terminal. -/
def removalCertificate {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isRemoval : routed.terminal = .removal) :
    RemovalCertificate capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | noRepetition _ => cases isRemoval
  | separation _ => cases isRemoval
  | removal certificate => exact certificate

end Routed

/-- One CT8 execution is one extension of the literal predecessor. -/
abbrev Stage
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public result of the canonical CT8 executor. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = stage.added.checks

namespace ExecutionResult

/-- Terminal derived from retained private route evidence. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Typed semantic output retained in the generated ledger entry. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.generatedOutcome

/-- Exact observable trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Recover the no-repetition certificate from a checked terminal equality. -/
def noRepetitionCertificate {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isNoRepetition : result.terminal = .noRepetition) :
    NoRepetitionCertificate capability result.stage.previous :=
  result.stage.added.noRepetitionCertificate isNoRepetition

/-- Recover the response-separation residual from a checked terminal equality. -/
def separationResidual {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isSeparation : result.terminal = .separation) :
    SeparationResidual capability result.stage.previous :=
  result.stage.added.separationResidual isSeparation

/-- Recover the strict-removal certificate from a checked terminal equality. -/
def removalCertificate {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isRemoval : result.terminal = .removal) :
    RemovalCertificate capability result.stage.previous :=
  result.stage.added.removalCertificate isRemoval

/-- Exact branch work is the count determined by the generated outcome. -/
theorem checks_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = outcomeChecks result.outcome :=
  result.checks_eq

/-- Actual branch work is bounded by the complete CT8 schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.sequenceAt result.stage.previous)
        (capability.responseContextsAt result.stage.previous).toEnumeration := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every generated execution satisfies the declared polynomial envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans
    (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT8 on one literal incoming accumulated ledger. -/
def run
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  .mk (Core.Residual.Ledger.extend previous routed) routed.trace routed.checks rfl

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT8
