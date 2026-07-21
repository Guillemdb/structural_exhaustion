import Hypostructure.CT15.Execution

/-!
# CT15 soundness, totality, and exact ledgers
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCoordinate} Previous}

namespace ExhaustiveIndependence

/-- Exhaustive index avoidance excludes every member of the queried schedule. -/
theorem noDependent {capability : Capability spec} {previous : Previous}
    (independence : ExhaustiveIndependence capability previous)
    (coordinate : spec.Coordinate previous)
    (member : coordinate ∈ (capability.coordinatesAt previous).values) :
    Not (spec.TargetDependent previous coordinate) := by
  obtain ⟨index, indexed⟩ :=
    ((capability.coordinatesAt previous).mem_iff_exists_index coordinate).mp
      member
  exact fun dependent => independence index (by simpa [indexed] using dependent)

end ExhaustiveIndependence

/-- Complete semantic claim advertised by each CT15 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .rankDrop, .rankDrop rank certificate =>
      rank.value = computedRank capability previous ∧
      spec.TargetDependent previous certificate.value ∧
      (forall coordinate,
        coordinate ∈ (capability.coordinatesAt previous).values.take
            certificate.index.1 ->
          Not (spec.TargetDependent previous coordinate))
  | .c4, .c4 rank _full ledger _certificate =>
      (forall coordinate,
        coordinate ∈ (capability.coordinatesAt previous).values ->
          Not (spec.TargetDependent previous coordinate)) ∧
      rank.value = targetRank capability previous ∧
      ledger.entries = ledgerEntries capability previous ∧
      ledger.total = ledgerTotal capability previous ∧
      spec.capacity previous < ledgerTotal capability previous
  | .fullRankLedger, .fullRankLedger rank _full ledger _residual =>
      (forall coordinate,
        coordinate ∈ (capability.coordinatesAt previous).values ->
          Not (spec.TargetDependent previous coordinate)) ∧
      rank.value = targetRank capability previous ∧
      ledger.entries = ledgerEntries capability previous ∧
      ledger.total = ledgerTotal capability previous ∧
      ledgerTotal capability previous <= spec.capacity previous

namespace Outcome

/-- Every framework-generated outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | rankDrop rank certificate =>
      exact ⟨rank.computed, certificate.sound, certificate.first⟩
  | c4 rank full ledger certificate =>
      exact ⟨full.independence.noDependent, full.full,
        ledger.entries_exact, ledger.total_exact, by
          simpa [ledger.total_exact] using certificate⟩
  | fullRankLedger rank full ledger residual =>
      exact ⟨full.independence.noDependent, full.full,
        ledger.entries_exact, ledger.total_exact, by
          simpa [ledger.total_exact] using residual⟩

/-- No terminal outside the three CT15 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .rankDrop ∨ terminal = .c4 ∨
      terminal = .fullRankLedger := by
  cases outcome with
  | rankDrop _ _ => exact Or.inl rfl
  | c4 _ _ _ _ => exact Or.inr (Or.inl rfl)
  | fullRankLedger _ _ _ _ => exact Or.inr (Or.inr rfl)

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
theorem run_verified (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT15 is total, traced, polynomially bounded, and retains the exact
predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uCoordinate} Previous)
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
theorem run_deterministic (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .rankDrop ∨ result.terminal = .c4 ∨
      result.terminal = .fullRankLedger :=
  result.outcome.terminal_exhaustive

/-- Generated ledger entries contain every queried coordinate exactly in its
incoming order. -/
theorem ledgerEntries_fst {capability : Capability spec}
    {previous : Previous} :
    (ledgerEntries capability previous).map Prod.fst =
      (capability.coordinatesAt previous).values := by
  simp [ledgerEntries, Function.comp_def]

end Hypostructure.CT15
