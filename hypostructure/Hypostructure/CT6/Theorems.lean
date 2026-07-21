import Hypostructure.CT6.Execution

/-!
# CT6 soundness, totality, and exact-ledger theorems
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uIndex, uData} Previous}

namespace FirstFailureResidual

/-- The selected index belongs to the exact predecessor-owned order. -/
theorem member {capability : Capability spec} {previous : Previous}
    (residual : FirstFailureResidual capability previous) :
    residual.hit.value ∈ (capability.failureOrderAt previous).values :=
  residual.hit.member

/-- The selected local condition genuinely fails. -/
theorem failed {capability : Capability spec} {previous : Previous}
    (residual : FirstFailureResidual capability previous) :
    spec.Failure previous residual.hit.value :=
  residual.hit.sound

/-- Every earlier scheduled condition is active. -/
theorem cleanPrefix {capability : Capability spec} {previous : Previous}
    (residual : FirstFailureResidual capability previous) :
    forall candidate,
      candidate ∈ (capability.failureOrderAt previous).values.take
        residual.hit.index.1 ->
      Not (spec.Failure previous candidate) :=
  residual.hit.first

end FirstFailureResidual

namespace ActiveLedgerResidual

/-- Every exact schedule index is certified active. -/
theorem activeAtIndex {capability : Capability spec} {previous : Previous}
    (residual : ActiveLedgerResidual capability previous)
    (index : Fin (capability.failureOrderAt previous).card) :
    Not (spec.Failure previous
      ((capability.failureOrderAt previous).get index)) :=
  residual.noFailure index

/-- Every value occurring in the predecessor-owned order is active. -/
theorem activeAt {capability : Capability spec} {previous : Previous}
    (residual : ActiveLedgerResidual capability previous)
    (candidate : spec.Index previous)
    (member : candidate ∈ (capability.failureOrderAt previous).values) :
    Not (spec.Failure previous candidate) := by
  obtain ⟨index, indexed⟩ :=
    ((capability.failureOrderAt previous).mem_iff_exists_index candidate).mp
      member
  intro failed
  exact residual.noFailure index (by simpa [indexed] using failed)

end ActiveLedgerResidual

/-- Active entries retain the incoming order exactly. -/
theorem activeEntries_fst {capability : Capability spec}
    {previous : Previous} :
    (activeEntries capability previous).map Prod.fst =
      (capability.failureOrderAt previous).values := by
  simp [activeEntries, Function.comp_def]

/-- Complete semantic claim advertised by each CT6 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .firstFailure, .firstFailure residual =>
      residual.hit.value ∈ (capability.failureOrderAt previous).values ∧
      spec.Failure previous residual.hit.value ∧
      (forall candidate,
        candidate ∈ (capability.failureOrderAt previous).values.take
          residual.hit.index.1 ->
        Not (spec.Failure previous candidate)) ∧
      residual.data =
        spec.failureData previous residual.hit.value residual.hit.holds
  | .activeLedger, .activeLedger residual =>
      residual.entries = activeEntries capability previous ∧
      residual.entries.map Prod.fst =
        (capability.failureOrderAt previous).values ∧
      residual.total = activeTotal capability previous ∧
      (forall index : Fin (capability.failureOrderAt previous).card,
        Not (spec.Failure previous
          ((capability.failureOrderAt previous).get index)))

namespace Outcome

/-- Every framework-generated CT6 outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | firstFailure residual =>
      exact ⟨residual.member, residual.failed, residual.cleanPrefix,
        residual.data_exact⟩
  | activeLedger residual =>
      exact ⟨residual.entries_exact,
        by simpa [residual.entries_exact] using
          (activeEntries_fst (capability := capability)
            (previous := previous)),
        residual.total_exact, residual.noFailure⟩

/-- A scheduled failure rules out the exhaustive active-ledger terminal. -/
theorem terminal_firstFailure_of_exists
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (existsFailure : Exists fun candidate =>
      candidate ∈ (capability.failureOrderAt previous).values ∧
        spec.Failure previous candidate) :
    terminal = .firstFailure := by
  obtain ⟨candidate, member, failed⟩ := existsFailure
  cases outcome with
  | firstFailure _ => rfl
  | activeLedger residual =>
      exact (residual.activeAt candidate member failed).elim

/-- Exhaustive activity rules out the first-failure terminal. -/
theorem terminal_activeLedger_of_noFailure
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (noFailure : Core.Finite.Search.Avoids
      (capability.failureOrderAt previous) (spec.Failure previous)) :
    terminal = .activeLedger := by
  cases outcome with
  | firstFailure residual =>
      exact (noFailure residual.hit.index residual.hit.holds).elim
  | activeLedger _ => rfl

/-- No terminal outside the two CT6 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .firstFailure ∨ terminal = .activeLedger := by
  cases outcome with
  | firstFailure _ => exact Or.inl rfl
  | activeLedger _ => exact Or.inr rfl

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

/-- Any scheduled failure forces the first-failure terminal. -/
theorem terminal_firstFailure_of_exists {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (existsFailure : Exists fun candidate =>
      candidate ∈
        (capability.failureOrderAt result.stage.previous).values ∧
      spec.Failure result.stage.previous candidate) :
    result.terminal = .firstFailure :=
  result.outcome.terminal_firstFailure_of_exists existsFailure

/-- Activity at every scheduled index forces the active-ledger terminal. -/
theorem terminal_activeLedger_of_noFailure {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (noFailure : Core.Finite.Search.Avoids
      (capability.failureOrderAt result.stage.previous)
      (spec.Failure result.stage.previous)) :
    result.terminal = .activeLedger :=
  result.outcome.terminal_activeLedger_of_noFailure noFailure

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT6 is total, exactly counted, exactly traced, polynomially bounded, and
retains its literal predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks = Core.Finite.Accounting.executionChecks
        (activityScan capability previous) ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_exact, result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic (spec : Spec.{uPrevious, uIndex, uData} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for one completed CT6 execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .firstFailure ∨ result.terminal = .activeLedger :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT6
