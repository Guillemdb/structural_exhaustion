import Erdos64EG.P13WeightedColdRestrictedPriorSemanticComparison
import Erdos64EG.P13WeightedColdRestrictedF1Handoff
import Erdos64EG.P13ColdGermLedger

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-!
# Conditional F5 germ on the original node-[153] edge

This module consumes the exact locally surviving corridor already constructed
on `[152] -> [153]`.  Terminal and repeated are only the geometric/semantic
inputs to F5, not `P13ColdGermLedger.ColdBoundedGerm`: the latter additionally
requires an actual proper atom and replacement, target-free/baseline/smaller
proofs, and a finite response table with symbolic coverage.  In the repeated
case the actual structural pair is sent through F2 and then F3; only universal
F2 followed by negative F3 reaches the still-open F5 producer.
-/

/-- Exact F1-negative fact supplied by the stage-major node-[153] runner. -/
abbrev F1Clear : Prop :=
  ∀ stage : package.Stage, ¬package.F1Stage stage

/-- The terminal F5 subcase is the whole literal component corridor. -/
structure TerminalF5Support {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (short : (package.coldStructuralCorridorProfile survivor).stages.values.length ≤
      (package.coldStructuralCorridorProfile survivor).stateBound) where
  runExact : package.runColdStructuralCorridor survivor =
    .terminal short
  wholeCorridorIsPath :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).IsPath
  wholeCorridorSupportBound :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).support.length ≤ QCold + 1
  f1Negative : ∀ stage : package.Stage, ¬package.F1Stage stage
  f4Negative : ∀ stage : package.Stage,
    ∃ complete : package.D6Complete ledger stage,
      package.runD6 ledger stage = .complete complete

/-- The repeated F5 subcase retains the exact repeated structural pair and the
two semantic negatives which alone permit it to pass F2 and F3. -/
structure RepeatedF5Support {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (negative :
      (package.repeatedMatchedPriorPiecePair survivor repetition).F3Negative) where
  runExact : package.runColdStructuralCorridor survivor =
    .repeated repetition
  pair : package.MatchedPriorPiecePair survivor
    repetition.second repetition.first
  pairExact : pair = package.repeatedMatchedPriorPiecePair survivor repetition
  spanBound : repetition.secondIndex - repetition.firstIndex ≤ QCold
  f2Universal : pair.UniversalTargetEquality
  f3Negative : pair.F3Negative
  f1Negative : ∀ stage : package.Stage, ¬package.F1Stage stage
  f4Negative : ∀ stage : package.Stage,
    ∃ complete : package.D6Complete ledger stage,
      package.runD6 ledger stage = .complete complete

/-- Construct the whole-corridor F5 payload from the literal terminal Core
outcome. -/
noncomputable def terminalF5Support {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (short : (package.coldStructuralCorridorProfile survivor).stages.values.length ≤
      (package.coldStructuralCorridorProfile survivor).stateBound)
    (runExact : package.runColdStructuralCorridor survivor = .terminal short) :
    package.TerminalF5Support survivor f1Clear short := by
  have positiveBound : package.positiveStages.values.length ≤ QCold := by
    simpa only [coldStructuralCorridorProfile] using short
  have stagesLength := package.stages_length
  have supportBound :
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).support.length ≤ QCold + 1 := by
    change (package.stages.values.drop 1).length ≤ QCold at positiveBound
    rw [List.length_drop, stagesLength] at positiveBound
    omega
  exact {
    runExact := runExact
    wholeCorridorIsPath :=
      InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath
        package.input
    wholeCorridorSupportBound := supportBound
    f1Negative := f1Clear
    f4Negative := fun stage =>
      ⟨(survivor.clear stage).priorComplete,
        (survivor.clear stage).d6Exact⟩
  }

/-- Construct repeated-state F5 only after the exact universal-F2 and
negative-F3 certificates. -/
noncomputable def repeatedF5Support {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (runExact : package.runColdStructuralCorridor survivor = .repeated repetition)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (negative :
      (package.repeatedMatchedPriorPiecePair survivor repetition).F3Negative) :
    package.RepeatedF5Support survivor f1Clear repetition universal negative := by
  let pair := package.repeatedMatchedPriorPiecePair survivor repetition
  have spanBound : repetition.secondIndex - repetition.firstIndex ≤ QCold := by
    simpa only [coldStructuralCorridorProfile] using repetition.span_le_bound
  exact {
    runExact := runExact
    pair := pair
    pairExact := rfl
    spanBound := spanBound
    f2Universal := universal
    f3Negative := negative
    f1Negative := f1Clear
    f4Negative := fun stage =>
      ⟨(survivor.clear stage).priorComplete,
        (survivor.clear stage).d6Exact⟩
  }

/-- Exhaustive conditional routing up to, but not including, the missing F5
`ColdBoundedGerm` constructor.  A repeated universal-F2/F3-compression result
is eliminated by the already verified replacement contradiction. -/
theorem terminalSupport_or_repeatedF2_or_repeatedSupport
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear) :
    (∃ short,
      package.runColdStructuralCorridor survivor = .terminal short ∧
        Nonempty (package.TerminalF5Support survivor f1Clear short)) ∨
    (∃ repetition distinction,
      package.runColdStructuralCorridor survivor = .repeated repetition ∧
        (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF2 =
          .distinction distinction) ∨
    (∃ repetition universal negative,
      package.runColdStructuralCorridor survivor = .repeated repetition ∧
        (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF2 =
          .universal universal ∧
        (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF3
            universal = .negative negative ∧
        Nonempty (package.RepeatedF5Support survivor f1Clear repetition
          universal negative)) := by
  classical
  rcases (package.coldStructuralCorridorProfile survivor).run_total with
    ⟨short, runExact⟩ | ⟨repetition, runExact⟩
  · exact .inl ⟨short, runExact,
      ⟨package.terminalF5Support survivor f1Clear short runExact⟩⟩
  · let pair := package.repeatedMatchedPriorPiecePair survivor repetition
    cases f2Exact : pair.classifyF2 with
    | distinction distinction =>
        exact .inr (.inl ⟨repetition, distinction, runExact, f2Exact⟩)
    | universal universal =>
        cases f3Exact : pair.classifyF3 universal with
        | compression compression =>
            exact False.elim (pair.f3_closes universal compression)
        | negative negative =>
            exact .inr (.inr ⟨repetition, universal, negative, runExact,
              f2Exact, f3Exact,
              ⟨package.repeatedF5Support survivor f1Clear repetition runExact
                universal negative⟩⟩)

/-- Exact exhaustive F5 support after the preceding stage-major predicates are
negative.  This is the paper's terminal-or-repeated structural alternative;
it does not manufacture the still-required `ColdBoundedGerm` response table
or a proper replacement atom. -/
theorem terminalSupport_or_repeatedSupport_of_f2_clear
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (f2Clear : ∀ repetition distinction,
      (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF2 ≠
        .distinction distinction) :
    (∃ short,
      package.runColdStructuralCorridor survivor = .terminal short ∧
        Nonempty (package.TerminalF5Support survivor f1Clear short)) ∨
    (∃ repetition universal negative,
      package.runColdStructuralCorridor survivor = .repeated repetition ∧
        (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF2 =
          .universal universal ∧
        (package.repeatedMatchedPriorPiecePair survivor repetition).classifyF3
            universal = .negative negative ∧
        Nonempty (package.RepeatedF5Support survivor f1Clear repetition
          universal negative)) := by
  rcases package.terminalSupport_or_repeatedF2_or_repeatedSupport
      survivor f1Clear with terminal | distinction | repeated
  · exact .inl terminal
  · rcases distinction with ⟨repetition, data, _runExact, classified⟩
    exact False.elim (f2Clear repetition data classified)
  · rcases repeated with
      ⟨repetition, universal, negative, runExact, f2Exact, f3Exact, support⟩
    exact .inr ⟨repetition, universal, negative, runExact, f2Exact, f3Exact,
      support⟩

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
