import Hypostructure.CT13.Search

/-!
# CT13 accumulated execution

The reference machine owns every computation and decision.  A completed run
adds one private routed value to the literal predecessor ledger; intermediate
search stages are not exposed as application-authored handoffs.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

/-- Exhaustive CT13 terminals. -/
inductive Terminal where
  | tierOne
  | overlap
  | deficit
  | reconciled
  deriving DecidableEq, Repr

/-- Audit nodes in canonical CT13 execution order. -/
inductive NodeId where
  | entry
  | payerSchedule
  | tierOneSearch
  | obstructionSchedule
  | fallbackSelection
  | tierTwoSchedule
  | overlapSearch
  | reconciliationLedger
  | comparison
  | tierOneTerminal
  | overlapTerminal
  | deficitTerminal
  | reconciledTerminal
  deriving DecidableEq, Repr

/-- Framework-generated terminal evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | tierOne (residual : TierOneResidual capability previous) :
      Outcome capability previous .tierOne
  | overlap (residual : OverlapResidual capability previous) :
      Outcome capability previous .overlap
  | deficit (residual : DeficitResidual capability previous) :
      Outcome capability previous .deficit
  | reconciled
      (certificate : ReconciliationCertificate capability previous) :
      Outcome capability previous .reconciled

namespace Outcome

/-- Observable canonical fallback, absent only on the tier-one terminal. -/
def selectedFallback? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal ->
      Option (spec.Obstruction previous)
  | .tierOne, .tierOne _residual => none
  | .overlap, .overlap residual => some residual.fallback.selected
  | .deficit, .deficit residual => some residual.ledger.fallback.selected
  | .reconciled, .reconciled certificate =>
      some certificate.ledger.fallback.selected

/-- Observable first overlap index, present only on the overlap terminal. -/
def overlapIndex? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Option Nat
  | .overlap, .overlap residual => some residual.hit.index.1
  | .tierOne, .tierOne _ => none
  | .deficit, .deficit _ => none
  | .reconciled, .reconciled _ => none

/-- Observable first overlapping payer pair. -/
def overlapPair? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal ->
      Option (spec.Payer previous × spec.Payer previous)
  | .overlap, .overlap residual => some residual.hit.value
  | .tierOne, .tierOne _ => none
  | .deficit, .deficit _ => none
  | .reconciled, .reconciled _ => none

end Outcome

/-- Terminal-indexed canonical CT13 trace. -/
inductive Trace : Terminal -> Type where
  | tierOne : Trace .tierOne
  | overlap : Trace .overlap
  | deficit : Trace .deficit
  | reconciled : Trace .reconciled

namespace Trace

/-- Observable node order of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .tierOne, .tierOne =>
      [.entry, .payerSchedule, .tierOneSearch, .tierOneTerminal]
  | .overlap, .overlap =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .overlapTerminal]
  | .deficit, .deficit =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .deficitTerminal]
  | .reconciled, .reconciled =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .reconciledTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .tierOne =>
      [.entry, .payerSchedule, .tierOneSearch, .tierOneTerminal]
  | .overlap =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .overlapTerminal]
  | .deficit =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .deficitTerminal]
  | .reconciled =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .reconciledTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .tierOne, .tierOne => rfl
  | .overlap, .overlap => rfl
  | .deficit, .deficit => rfl
  | .reconciled, .reconciled => rfl

end Trace

/-- Private framework route selected by the deterministic reference machine. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Execute primary search, fallback selection, reconciliation, and comparison. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let primary := routeTierOne capability previous
  match primary.added with
  | .yesBranch hasTierOne =>
      .mk .tierOne (.tierOne
        (primary.previous.hitOfHasHit hasTierOne))
  | .noBranch absence =>
      let fallback := computeFallback capability previous absence
      let reconciliation := routeOverlap capability previous fallback
      match reconciliation.added with
      | .yesBranch hasOverlap =>
          .mk .overlap (.overlap
            (overlapResidual capability previous fallback
              (reconciliation.previous.hitOfHasHit hasOverlap)))
      | .noBranch overlapFree =>
          let ledger := buildReconciliationLedger capability previous
            fallback overlapFree
          let comparison := compare capability previous ledger
          match comparison.added with
          | .yesBranch deficit =>
              .mk .deficit (.deficit
                (deficitResidual capability previous ledger (by
                  have exactDeficit := deficit
                  rw [show comparison.previous = ledger from rfl] at exactDeficit
                  exact exactDeficit)))
          | .noBranch covers =>
              .mk .reconciled (.reconciled
                (reconciliationCertificate capability previous ledger (by
                  have exactCovers := covers
                  rw [show comparison.previous = ledger from rfl] at exactCovers
                  exact exactCovers)))

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | tierOne _ => exact .tierOne
  | overlap _ => exact .overlap
  | deficit _ => exact .deficit
  | reconciled _ => exact .reconciled

/-- Unique typed trace selected by a private routed result. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive checks performed on each terminal branch. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .tierOne, .tierOne residual => residual.index.1 + 1
  | .overlap, .overlap residual =>
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          residual.hit.index.1 + 1
  | .deficit, .deficit residual =>
      let tierTwo := selectedTierTwo capability previous
        residual.ledger.fallback
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1
  | .reconciled, .reconciled certificate =>
      let tierTwo := selectedTierTwo capability previous
        certificate.ledger.fallback
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1

/-- Branch-exact work is bounded by the complete inherited schedule envelope. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.payersAt previous)
        (capability.obstructionsAt previous)
        (capability.tierTwo.read previous) := by
  cases outcome with
  | tierOne residual =>
      have inspected : residual.index.1 + 1 <=
          (capability.payersAt previous).card :=
        Nat.succ_le_iff.mpr residual.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | overlap residual =>
      have inspected : residual.hit.index.1 + 1 <=
          (reconciliationPairs capability previous residual.fallback).card :=
        Nat.succ_le_iff.mpr residual.hit.index.isLt
      have tierLe := selectedTierTwo_card_le_sum capability previous
        residual.fallback
      have squareLe :
          (selectedTierTwo capability previous residual.fallback).card *
              (selectedTierTwo capability previous residual.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      have pairInspected : residual.hit.index.1 + 1 <=
          (selectedTierTwo capability previous residual.fallback).card *
            (selectedTierTwo capability previous residual.fallback).card := by
        change residual.hit.index.1 + 1 <=
          ((selectedTierTwo capability previous residual.fallback).product
            (selectedTierTwo capability previous residual.fallback)).card at inspected
        rw [Core.Finite.Enumeration.card_product] at inspected
        exact inspected
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega
  | deficit residual =>
      have tierLe := selectedTierTwo_card_le_sum capability previous
        residual.ledger.fallback
      have squareLe :
          (selectedTierTwo capability previous residual.ledger.fallback).card *
              (selectedTierTwo capability previous residual.ledger.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega
  | reconciled certificate =>
      have tierLe := selectedTierTwo_card_le_sum capability previous
        certificate.ledger.fallback
      have squareLe :
          (selectedTierTwo capability previous certificate.ledger.fallback).card *
              (selectedTierTwo capability previous certificate.ledger.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega

/-- One CT13 execution is one extension of the literal incoming ledger. -/
abbrev Stage
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public CT13 execution. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Observable canonical fallback, absent only on the tier-one terminal. -/
def selectedFallback? {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Option (spec.Obstruction result.stage.previous) :=
  result.outcome.selectedFallback?

/-- Observable first overlap index, present only on the overlap terminal. -/
def overlapIndex? {capability : Capability spec}
    (result : ExecutionResult spec capability) : Option Nat :=
  result.outcome.overlapIndex?

/-- Observable first overlapping payer pair, present only on the overlap
terminal. -/
def overlapPair? {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Option (spec.Payer result.stage.previous ×
      spec.Payer result.stage.previous) :=
  result.outcome.overlapPair?

theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.payersAt result.stage.previous)
        (capability.obstructionsAt result.stage.previous)
        (capability.tierTwo.read result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT13 on one literal predecessor ledger. -/
def run
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
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
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT13
