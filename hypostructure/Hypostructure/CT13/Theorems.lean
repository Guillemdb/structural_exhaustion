import Hypostructure.CT13.Execution

/-!
# CT13 soundness, totality, and ledger theorems
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

namespace TierOneAbsenceState

/-- Exhaustive primary-search failure excludes every payer in the inherited
schedule, and no payer outside that schedule is asserted absent. -/
theorem absentAt {capability : Capability spec} {previous : Previous}
    (absence : TierOneAbsenceState capability previous)
    (payer : spec.Payer previous)
    (member : payer ∈ (capability.payersAt previous).values) :
    Not (spec.Eligible previous payer) := by
  obtain ⟨index, indexed⟩ :=
    ((capability.payersAt previous).mem_iff_exists_index payer).mp member
  have absent := absence index
  rw [indexed] at absent
  exact absent

end TierOneAbsenceState

namespace OverlapFreeState

/-- Exhaustive reconciliation excludes every overlap in the exact derived
pair order. -/
theorem absentAt {capability : Capability spec} {previous : Previous}
    {fallback : FallbackState capability previous}
    (clean : OverlapFreeState capability previous fallback)
    (pair : spec.Payer previous × spec.Payer previous)
    (member : pair ∈
      (reconciliationPairs capability previous fallback).values) :
    Not (ResourceOverlap (spec := spec) previous pair) := by
  obtain ⟨index, indexed⟩ :=
    ((reconciliationPairs capability previous fallback).mem_iff_exists_index
      pair).mp member
  have absent := clean index
  rw [indexed] at absent
  exact absent

end OverlapFreeState

/-- Exact semantic content of a generated fallback. -/
def FallbackClaim {capability : Capability spec} {previous : Previous}
    (fallback : FallbackState capability previous) : Prop :=
  (forall payer,
      payer ∈ (capability.payersAt previous).values ->
        Not (spec.Eligible previous payer)) ∧
  fallback.selected ∈
    (capability.obstructionsAt previous).enumeration.values ∧
  fallback.selected = selectMin (spec.obstructionCost previous)
    (capability.obstructionsAt previous).fallbackDefault
    (capability.obstructionsAt previous).remaining ∧
  forall obstruction,
    obstruction ∈
      (capability.obstructionsAt previous).enumeration.values ->
      spec.obstructionCost previous fallback.selected <=
        spec.obstructionCost previous obstruction

namespace FallbackState

theorem verified {capability : Capability spec} {previous : Previous}
    (fallback : FallbackState capability previous) :
    FallbackClaim fallback :=
  ⟨fun payer member => fallback.tierOneAbsent.absentAt payer member,
    fallback.selected_member, fallback.canonical, fallback.minimal⟩

end FallbackState

/-- Exact semantic content of a generated reconciliation ledger. -/
def ReconciliationClaim {capability : Capability spec} {previous : Previous}
    (ledger : ReconciliationLedger capability previous) : Prop :=
  FallbackClaim ledger.fallback ∧
  ledger.entries = reconciliationEntries capability previous ledger.fallback ∧
  ledger.capacity = totalCharge capability previous ledger.fallback ∧
  forall pair,
    pair ∈ (reconciliationPairs capability previous ledger.fallback).values ->
      Not (ResourceOverlap (spec := spec) previous pair)

namespace ReconciliationLedger

theorem verified {capability : Capability spec} {previous : Previous}
    (ledger : ReconciliationLedger capability previous) :
    ReconciliationClaim ledger :=
  ⟨ledger.fallback.verified, ledger.entries_exact, ledger.capacity_exact,
    fun pair member => ledger.overlapFree.absentAt pair member⟩

end ReconciliationLedger

/-- Complete semantic claim advertised by each CT13 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .tierOne, .tierOne residual =>
      residual.value ∈ (capability.payersAt previous).values ∧
      spec.Eligible previous residual.value ∧
      (forall payer,
        payer ∈ (capability.payersAt previous).values.take residual.index.1 ->
          Not (spec.Eligible previous payer))
  | .overlap, .overlap residual =>
      FallbackClaim residual.fallback ∧
      residual.hit.value ∈
        (reconciliationPairs capability previous residual.fallback).values ∧
      ResourceOverlap (spec := spec) previous residual.hit.value ∧
      (forall pair,
        pair ∈ (reconciliationPairs capability previous residual.fallback).values.take
          residual.hit.index.1 ->
          Not (ResourceOverlap (spec := spec) previous pair))
  | .deficit, .deficit residual =>
      ReconciliationClaim residual.ledger ∧
      residual.ledger.capacity < spec.demand previous
  | .reconciled, .reconciled certificate =>
      ReconciliationClaim certificate.ledger ∧
      spec.demand previous <= certificate.ledger.capacity

namespace Outcome

/-- Every framework-generated outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | tierOne residual =>
      exact ⟨residual.member, residual.sound, residual.first⟩
  | overlap residual =>
      exact ⟨residual.fallback.verified, residual.hit.member,
        residual.hit.sound, residual.hit.first⟩
  | deficit residual =>
      exact ⟨residual.ledger.verified, residual.deficit⟩
  | reconciled certificate =>
      exact ⟨certificate.ledger.verified, certificate.covers⟩

/-- No terminal outside the four CT13 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .tierOne ∨ terminal = .overlap ∨
      terminal = .deficit ∨ terminal = .reconciled := by
  cases outcome with
  | tierOne _ => exact Or.inl rfl
  | overlap _ => exact Or.inr (Or.inl rfl)
  | deficit _ => exact Or.inr (Or.inr (Or.inl rfl))
  | reconciled _ => exact Or.inr (Or.inr (Or.inr rfl))

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete observable trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT13 is total, exactly traced, polynomially bounded, and retains the
literal predecessor. -/
theorem run_total
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .tierOne ∨ result.terminal = .overlap ∨
      result.terminal = .deficit ∨ result.terminal = .reconciled :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT13
