import Hypostructure.CT14.Execution

/-!
# CT14 soundness, totality, and ledger theorems
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uMember, uLabel} Previous}

namespace CapacityComplete

/-- Exhaustive capacity-scan failure gives an actual finite capacity for each
member of the exact incoming schedule. -/
theorem present {capability : Capability spec} {previous : Previous}
    (complete : CapacityComplete capability previous)
    (member : spec.Member previous)
    (memberOf : member ∈ (capability.membersAt previous).values) :
    Exists fun value => spec.memberCapacity previous member = some value := by
  obtain ⟨index, indexed⟩ :=
    ((capability.membersAt previous).mem_iff_exists_index member).mp memberOf
  cases found : spec.memberCapacity previous member with
  | none =>
      have missing : spec.memberCapacity previous
          ((capability.membersAt previous).get index) = none := by
        simpa [indexed] using found
      exact (complete index missing).elim
  | some value => exact ⟨value, rfl⟩

end CapacityComplete

namespace LabelComplete

/-- Exhaustive label-scan failure gives an actual label for each member of
the exact incoming schedule. -/
theorem present {capability : Capability spec} {previous : Previous}
    (complete : LabelComplete capability previous)
    (member : spec.Member previous)
    (memberOf : member ∈ (capability.membersAt previous).values) :
    Exists fun label => spec.memberLabel previous member = some label := by
  obtain ⟨index, indexed⟩ :=
    ((capability.membersAt previous).mem_iff_exists_index member).mp memberOf
  cases found : spec.memberLabel previous member with
  | none =>
      have missing : spec.memberLabel previous
          ((capability.membersAt previous).get index) = none := by
        simpa [indexed] using found
      exact (complete index missing).elim
  | some label => exact ⟨label, rfl⟩

end LabelComplete

namespace MultiplicityLedger

/-- Every generated label fibre is bounded by the exact member schedule. -/
theorem counts_le_card {capability : Capability spec} {previous : Previous}
    (ledger : MultiplicityLedger capability previous)
    (label : spec.Label previous) :
    ledger.counts label <= (capability.membersAt previous).card := by
  rw [ledger.counts_exact]
  exact Core.Finite.Accounting.fibreCount_le_card
    (capability.membersAt previous) (spec.memberLabel previous) (some label)
      (by
        letI : DecidableEq (spec.Label previous) :=
          capability.labelDecidableEq previous
        exact inferInstance)

end MultiplicityLedger

/-- Complete semantic claim advertised by each CT14 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .unboundedMember, .unboundedMember lower residual =>
      lower.entries = lowerMassEntries capability previous ∧
      lower.total = lowerMass capability previous ∧
      residual.value ∈ (capability.membersAt previous).values ∧
      spec.memberCapacity previous residual.value = none ∧
      (forall member,
        member ∈ (capability.membersAt previous).values.take residual.index.1 ->
          spec.memberCapacity previous member ≠ none)
  | .missingLabel, .missingLabel lower _bounded residual =>
      lower.entries = lowerMassEntries capability previous ∧
      lower.total = lowerMass capability previous ∧
      (forall member,
        member ∈ (capability.membersAt previous).values ->
          Exists fun value =>
            spec.memberCapacity previous member = some value) ∧
      residual.value ∈ (capability.membersAt previous).values ∧
      spec.memberLabel previous residual.value = none ∧
      (forall member,
        member ∈ (capability.membersAt previous).values.take residual.index.1 ->
          spec.memberLabel previous member ≠ none)
  | .aggregate, .aggregate ledger _certificate =>
      ledger.lower.entries = lowerMassEntries capability previous ∧
      ledger.lower.total = lowerMass capability previous ∧
      ledger.capacity.entries = capacityEntries capability previous ∧
      ledger.capacity.total = upperCapacity capability previous ∧
      (forall label, ledger.multiplicity.counts label =
        multiplicity capability previous label) ∧
      (forall member,
        member ∈ (capability.membersAt previous).values ->
          Exists fun value =>
            spec.memberCapacity previous member = some value) ∧
      (forall member,
        member ∈ (capability.membersAt previous).values ->
          Exists fun label => spec.memberLabel previous member = some label) ∧
      upperCapacity capability previous < lowerMass capability previous
  | .capacity, .capacity ledger _residual =>
      ledger.lower.entries = lowerMassEntries capability previous ∧
      ledger.lower.total = lowerMass capability previous ∧
      ledger.capacity.entries = capacityEntries capability previous ∧
      ledger.capacity.total = upperCapacity capability previous ∧
      (forall label, ledger.multiplicity.counts label =
        multiplicity capability previous label) ∧
      (forall member,
        member ∈ (capability.membersAt previous).values ->
          Exists fun value =>
            spec.memberCapacity previous member = some value) ∧
      (forall member,
        member ∈ (capability.membersAt previous).values ->
          Exists fun label => spec.memberLabel previous member = some label) ∧
      lowerMass capability previous <= upperCapacity capability previous

namespace Outcome

/-- Every framework-generated outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | unboundedMember lower residual =>
      exact ⟨lower.entries_exact, lower.total_exact, residual.member,
        residual.sound, residual.first⟩
  | missingLabel lower bounded residual =>
      exact ⟨lower.entries_exact, lower.total_exact,
        fun member memberOf => bounded.present member memberOf,
        residual.member, residual.sound, residual.first⟩
  | aggregate ledger certificate =>
      exact ⟨ledger.lower.entries_exact, ledger.lower.total_exact,
        ledger.capacity.entries_exact, ledger.capacity.total_exact,
        ledger.multiplicity.counts_exact,
        fun member memberOf => ledger.capacity.complete.present member memberOf,
        fun member memberOf =>
          ledger.multiplicity.complete.present member memberOf,
        by
          simpa [ledger.capacity.total_exact, ledger.lower.total_exact] using
            certificate⟩
  | capacity ledger residual =>
      exact ⟨ledger.lower.entries_exact, ledger.lower.total_exact,
        ledger.capacity.entries_exact, ledger.capacity.total_exact,
        ledger.multiplicity.counts_exact,
        fun member memberOf => ledger.capacity.complete.present member memberOf,
        fun member memberOf =>
          ledger.multiplicity.complete.present member memberOf,
        by
          simpa [ledger.capacity.total_exact, ledger.lower.total_exact] using
            residual⟩

/-- No terminal outside the four CT14 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .unboundedMember ∨ terminal = .missingLabel ∨
      terminal = .aggregate ∨ terminal = .capacity := by
  cases outcome with
  | unboundedMember _ _ => exact Or.inl rfl
  | missingLabel _ _ _ => exact Or.inr (Or.inl rfl)
  | aggregate _ _ => exact Or.inr (Or.inr (Or.inl rfl))
  | capacity _ _ => exact Or.inr (Or.inr (Or.inr rfl))

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
theorem run_verified (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT14 is total, exactly traced, polynomially bounded, and retains the
literal predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uMember, uLabel} Previous)
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
theorem run_deterministic (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .unboundedMember ∨ result.terminal = .missingLabel ∨
      result.terminal = .aggregate ∨ result.terminal = .capacity :=
  result.outcome.terminal_exhaustive

/-- Lower ledger entries preserve the incoming member order exactly. -/
theorem lowerMassEntries_fst {capability : Capability spec}
    {previous : Previous} :
    (lowerMassEntries capability previous).map Prod.fst =
      (capability.membersAt previous).values := by
  simp [lowerMassEntries, Function.comp_def]

/-- Capacity ledger entries preserve the incoming member order exactly. -/
theorem capacityEntries_fst {capability : Capability spec}
    {previous : Previous} :
    (capacityEntries capability previous).map Prod.fst =
      (capability.membersAt previous).values := by
  simp [capacityEntries, Function.comp_def]

end Hypostructure.CT14
