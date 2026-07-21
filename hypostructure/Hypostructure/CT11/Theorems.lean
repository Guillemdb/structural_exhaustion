import Hypostructure.CT11.Execution

/-!
# CT11 soundness, totality, and work theorems
-/

namespace Hypostructure.CT11

universe uPrevious uCell

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCell} Previous}

namespace AdmissibilityGapResidual

/-- The selected gap belongs to the exact predecessor-owned order. -/
theorem member {capability : Capability spec} {previous : Previous}
    (residual : AdmissibilityGapResidual capability previous) :
    residual.value ∈ (capability.cellsAt previous).values :=
  Core.Finite.Search.IndexedHit.member residual

/-- The selected cell is genuinely inadmissible. -/
theorem inadmissible {capability : Capability spec} {previous : Previous}
    (residual : AdmissibilityGapResidual capability previous) :
    Not (spec.Admissible previous residual.value) :=
  Core.Finite.Search.IndexedHit.sound residual

/-- Every earlier cell is admissible, so the selected gap is canonical. -/
theorem prefixAdmissible {capability : Capability spec}
    {previous : Previous}
    (residual : AdmissibilityGapResidual capability previous) :
    forall candidate,
      candidate ∈ (capability.cellsAt previous).values.take residual.index.1 ->
        spec.Admissible previous candidate := by
  intro candidate member
  match capability.admissibleDecidable previous candidate with
  | .isTrue admissible => exact admissible
  | .isFalse inadmissible =>
      exact (Core.Finite.Search.IndexedHit.first residual
        candidate member inadmissible).elim

end AdmissibilityGapResidual

namespace AdmissibleDecomposition

/-- Every member of the exact incoming order is admissible. -/
theorem admissibleAt {capability : Capability spec} {previous : Previous}
    (decomposition : AdmissibleDecomposition capability previous)
    (cell : spec.Cell previous)
    (member : cell ∈ (capability.cellsAt previous).values) :
    spec.Admissible previous cell :=
  decomposition.admissible cell member

end AdmissibleDecomposition

namespace LocalizedDeficitResidual

/-- Selected localized cell. -/
def cell {capability : Capability spec} {previous : Previous}
    (residual : LocalizedDeficitResidual capability previous) :
    spec.Cell previous :=
  residual.hit.value

/-- The selected cell belongs to the exact predecessor-owned order. -/
theorem member {capability : Capability spec} {previous : Previous}
    (residual : LocalizedDeficitResidual capability previous) :
    residual.cell ∈ (capability.cellsAt previous).values :=
  residual.hit.member

/-- The localized cell is admissible. -/
theorem isAdmissible {capability : Capability spec} {previous : Previous}
    (residual : LocalizedDeficitResidual capability previous) :
    spec.Admissible previous residual.cell :=
  residual.admissible.admissibleAt residual.cell residual.member

/-- The localized cell has strict negative local budget. -/
theorem negative {capability : Capability spec} {previous : Previous}
    (residual : LocalizedDeficitResidual capability previous) :
    spec.localBudget previous residual.cell < 0 :=
  residual.hit.sound

/-- Every earlier cell has nonnegative local budget. -/
theorem prefixNonnegative {capability : Capability spec}
    {previous : Previous}
    (residual : LocalizedDeficitResidual capability previous) :
    forall candidate,
      candidate ∈
          (capability.cellsAt previous).values.take residual.hit.index.1 ->
        0 <= spec.localBudget previous candidate := by
  intro candidate member
  exact le_of_not_gt (residual.hit.first candidate member)

end LocalizedDeficitResidual

/-- Complete semantic claim advertised by each CT11 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .admissibilityGap, .admissibilityGap residual =>
      residual.value ∈ (capability.cellsAt previous).values ∧
      Not (spec.Admissible previous residual.value) ∧
      (forall candidate,
        candidate ∈
            (capability.cellsAt previous).values.take residual.index.1 ->
          spec.Admissible previous candidate)
  | .localizedDeficit, .localizedDeficit residual =>
      (forall cell,
        cell ∈ (capability.cellsAt previous).values ->
          spec.Admissible previous cell) ∧
      residual.cell ∈ (capability.cellsAt previous).values ∧
      spec.Admissible previous residual.cell ∧
      spec.localBudget previous residual.cell < 0 ∧
      (forall candidate,
        candidate ∈
            (capability.cellsAt previous).values.take residual.hit.index.1 ->
          0 <= spec.localBudget previous candidate) ∧
      ((capability.cellsAt previous).values.map
        (spec.localBudget previous)).sum < 0

namespace Outcome

/-- Every framework-generated CT11 outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | admissibilityGap residual =>
      exact ⟨residual.member, residual.inadmissible,
        residual.prefixAdmissible⟩
  | localizedDeficit residual =>
      exact ⟨residual.admissible.admissible, residual.member,
        residual.isAdmissible, residual.negative,
        residual.prefixNonnegative, capability.negativeTotalAt previous⟩

/-- A scheduled inadmissible cell forces the gap terminal. -/
theorem terminal_admissibilityGap_of_exists
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (existsGap : Exists fun cell =>
      cell ∈ (capability.cellsAt previous).values ∧
        Not (spec.Admissible previous cell)) :
    terminal = .admissibilityGap := by
  obtain ⟨cell, member, inadmissible⟩ := existsGap
  cases outcome with
  | admissibilityGap _ => rfl
  | localizedDeficit residual =>
      exact (inadmissible
        (residual.admissible.admissibleAt cell member)).elim

/-- Admissibility of every scheduled cell forces localization. -/
theorem terminal_localizedDeficit_of_all_admissible
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (allAdmissible : forall cell,
      cell ∈ (capability.cellsAt previous).values ->
        spec.Admissible previous cell) :
    terminal = .localizedDeficit := by
  cases outcome with
  | admissibilityGap residual =>
      exact (residual.inadmissible
        (allAdmissible residual.value residual.member)).elim
  | localizedDeficit _ => rfl

/-- No terminal outside the two CT11 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .admissibilityGap ∨ terminal = .localizedDeficit := by
  cases outcome with
  | admissibilityGap _ => exact Or.inl rfl
  | localizedDeficit _ => exact Or.inr rfl

/-- Recover typed gap evidence from a terminal equality. -/
def gapResidual {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (isGap : terminal = .admissibilityGap) :
    AdmissibilityGapResidual capability previous := by
  cases outcome with
  | admissibilityGap residual => exact residual
  | localizedDeficit _ => cases isGap

/-- Recover typed localized-deficit evidence from a terminal equality. -/
def localizedResidual {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (isLocalized : terminal = .localizedDeficit) :
    LocalizedDeficitResidual capability previous := by
  cases outcome with
  | admissibilityGap _ => cases isLocalized
  | localizedDeficit residual => exact residual

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

/-- Recover typed gap evidence from a completed execution. -/
def gapResidual {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isGap : result.terminal = .admissibilityGap) :
    AdmissibilityGapResidual capability result.stage.previous :=
  result.outcome.gapResidual isGap

/-- Recover typed localized evidence from a completed execution. -/
def localizedResidual {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isLocalized : result.terminal = .localizedDeficit) :
    LocalizedDeficitResidual capability result.stage.previous :=
  result.outcome.localizedResidual isLocalized

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT11 is total, exactly counted, exactly traced, polynomially bounded, and
retains its literal predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks = outcomeChecks result.outcome ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_exact, result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic (spec : Spec.{uPrevious, uCell} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for one completed CT11 execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .admissibilityGap ∨
      result.terminal = .localizedDeficit :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT11
