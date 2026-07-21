import Hypostructure.CT9.Execution

/-!
# CT9 soundness, totality, and finite-partition theorems
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}

/-- Every incoming item belongs to the fibre named by its authored label. -/
theorem mem_own_fibre {capability : Capability spec} {previous : Previous}
    (item : spec.Item previous)
    (member : item ∈ (capability.itemsAt previous).values) :
    item ∈ fibre capability previous (spec.label previous item) := by
  simp [fibre, member]

/-- Distinct generated label fibres are disjoint. -/
theorem fibre_disjoint {capability : Capability spec} {previous : Previous}
    {left right : spec.Label previous} (different : left ≠ right) :
    forall item,
      item ∈ fibre capability previous left ->
      item ∈ fibre capability previous right -> False := by
  intro item inLeft inRight
  simp [fibre] at inLeft inRight
  exact different (inLeft.2.symm.trans inRight.2)

/-- Every computed fibre is bounded by the predecessor-owned item count. -/
theorem fibreCount_le_itemCount {capability : Capability spec}
    {previous : Previous} (label : spec.Label previous) :
    fibreCount capability previous label <=
      (capability.itemsAt previous).card := by
  unfold fibreCount fibre Core.Finite.Enumeration.card
  exact List.length_filter_le _ _

/-- Exact no-overcounting identity.  The complete label family partitions
the predecessor-owned item schedule with no loss and no duplication. -/
theorem cardinality_eq_sum_fibreCount {capability : Capability spec}
    {previous : Previous} :
    (capability.itemsAt previous).card =
      ((capability.labelScheduleAt previous).values.map
        (fibreCount capability previous)).sum := by
  letI : DecidableEq (spec.Label previous) :=
    (capability.labelScheduleAt previous).decEq
  letI : DecidableEq (spec.Item previous) :=
    (capability.itemsAt previous).decEq
  have itemCard : (capability.itemsAt previous).toFinset.card =
      (capability.itemsAt previous).values.length :=
    List.toFinset_card_of_nodup (capability.itemsAt previous).nodup
  have mapsTo :
      ((capability.itemsAt previous).toFinset : Set (spec.Item previous)).MapsTo
        (spec.label previous)
        (capability.labelScheduleAt previous).toFinset := by
    intro item _member
    exact List.mem_toFinset.mpr
      ((capability.labelsAt previous).complete (spec.label previous item))
  have partitionCard := Finset.card_eq_sum_card_fiberwise mapsTo
  rw [itemCard] at partitionCard
  change (capability.itemsAt previous).values.length = _
  rw [← List.sum_toFinset (fibreCount capability previous)
    (capability.labelScheduleAt previous).nodup]
  rw [partitionCard]
  apply Finset.sum_congr rfl
  intro label _labelMember
  unfold fibreCount fibre
  rw [← List.toFinset_card_of_nodup
    ((capability.itemsAt previous).nodup.filter fun item =>
      spec.label previous item = label)]
  congr 1
  ext item
  simp [Core.Finite.Enumeration.toFinset]

namespace BoundedCertificate

/-- Pointwise fibre bounds imply the exact global capacity bound. -/
theorem cardinality_le_totalCapacity {capability : Capability spec}
    {previous : Previous}
    (certificate : BoundedCertificate capability previous) :
    (capability.itemsAt previous).card <=
      totalCapacity capability previous := by
  rw [cardinality_eq_sum_fibreCount]
  unfold totalCapacity
  apply List.sum_le_sum
  intro label _member
  rw [← certificate.partition.count_exact label]
  exact certificate.bounded label

/-- Global excess is incompatible with a bounded partition. -/
theorem false_of_totalCapacity_lt_cardinality
    {capability : Capability spec} {previous : Previous}
    (certificate : BoundedCertificate capability previous)
    (tooMany : totalCapacity capability previous <
      (capability.itemsAt previous).card) : False :=
  (Nat.not_lt_of_ge certificate.cardinality_le_totalCapacity) tooMany

end BoundedCertificate

/-- Semantic injectivity of the label map on the supplied items bounds every
generated fibre by one. -/
theorem fibreCount_le_one_of_label_injective_on_items
    {capability : Capability spec} {previous : Previous}
    (injectiveOnItems : forall {first second : spec.Item previous},
      first ∈ (capability.itemsAt previous).values ->
      second ∈ (capability.itemsAt previous).values ->
      spec.label previous first = spec.label previous second ->
      first = second) :
    forall label, fibreCount capability previous label <= 1 := by
  letI : DecidableEq (spec.Label previous) :=
    (capability.labelScheduleAt previous).decEq
  letI : DecidableEq (spec.Item previous) :=
    (capability.itemsAt previous).decEq
  intro label
  let values := fibre capability previous label
  have valuesNodup : values.Nodup := by
    exact (capability.itemsAt previous).nodup.filter _
  change values.length <= 1
  rw [← List.toFinset_card_of_nodup valuesNodup]
  rw [Finset.card_le_one_iff]
  intro first second firstMem secondMem
  have firstFiltered :
      first ∈ (capability.itemsAt previous).values ∧
        spec.label previous first = label := by
    simpa [values, fibre] using firstMem
  have secondFiltered :
      second ∈ (capability.itemsAt previous).values ∧
        spec.label previous second = label := by
    simpa [values, fibre] using secondMem
  exact injectiveOnItems firstFiltered.1 secondFiltered.1
    (firstFiltered.2.trans secondFiltered.2.symm)

/-- Semantic absence makes one exact generated fibre empty. -/
theorem fibreCount_eq_zero_of_label_absent
    {capability : Capability spec} {previous : Previous}
    (label : spec.Label previous)
    (absent : forall item,
      item ∈ (capability.itemsAt previous).values ->
        spec.label previous item ≠ label) :
    fibreCount capability previous label = 0 := by
  letI : DecidableEq (spec.Label previous) :=
    (capability.labelScheduleAt previous).decEq
  unfold fibreCount fibre
  rw [List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro item itemMem
  simpa using absent item itemMem

/-- Complete semantic claim advertised by each CT9 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .overloaded, .overloaded partition residual =>
      residual.label ∈ (capability.labelScheduleAt previous).values ∧
      spec.capacity previous residual.label <
        partition.count residual.label ∧
      (forall label,
        label ∈ (capability.labelScheduleAt previous).values.take
          residual.index.1 ->
        partition.count label <= spec.capacity previous label)
  | .bounded, .bounded certificate =>
      forall label : spec.Label previous,
        certificate.partition.count label <= spec.capacity previous label

/-- Public package for the overload evidence retained by one exact result. -/
structure SelectedOverload (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  partition : Partition capability previous
  residual : OverloadResidual capability previous partition

namespace Outcome

/-- Every generated outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | overloaded partition residual =>
      exact ⟨residual.scheduled, residual.overloaded,
        fun label member => Nat.le_of_not_gt (residual.first label member)⟩
  | bounded certificate =>
      exact certificate.bounded

/-- No terminal outside the CT9 dichotomy is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .overloaded ∨ terminal = .bounded := by
  cases outcome with
  | overloaded _partition _residual => exact Or.inl rfl
  | bounded _certificate => exact Or.inr rfl

/-- Extract the selected partition and first overload from terminal-indexed
evidence. -/
def selectedOverloadOfTerminalEq {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal)
    (terminalEq : terminal = .overloaded) :
    SelectedOverload capability previous := by
  cases outcome with
  | overloaded partition residual =>
      exact .mk partition residual
  | bounded certificate =>
      simp at terminalEq

/-- A bounded outcome contradicts strict global excess. -/
theorem terminal_overloaded_of_totalCapacity_lt_cardinality
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (tooMany : totalCapacity capability previous <
      (capability.itemsAt previous).card) :
    terminal = .overloaded := by
  cases outcome with
  | overloaded partition residual => rfl
  | bounded certificate =>
      exact (certificate.false_of_totalCapacity_lt_cardinality tooMany).elim

/-- Pointwise fibre bounds rule out an overloaded outcome. -/
theorem terminal_bounded_of_bounded
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (bounded : forall label : spec.Label previous,
      fibreCount capability previous label <=
        spec.capacity previous label) :
    terminal = .bounded := by
  cases outcome with
  | overloaded partition residual =>
      have exactCount := partition.count_exact residual.label
      have notOverloaded :
          partition.count residual.label <=
            spec.capacity previous residual.label := by
        rw [exactCount]
        exact bounded residual.label
      exact (Nat.not_lt_of_ge notOverloaded residual.overloaded).elim
  | bounded certificate => rfl

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

/-- Extract the exact selected partition and first overloaded label. -/
def selectedOverloadOfTerminalEq {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (terminalEq : result.terminal = .overloaded) :
    SelectedOverload capability result.stage.previous :=
  result.outcome.selectedOverloadOfTerminalEq terminalEq

/-- Global excess forces this exact execution to its overload terminal. -/
theorem terminal_overloaded_of_totalCapacity_lt_cardinality
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (tooMany : totalCapacity capability result.stage.previous <
      (capability.itemsAt result.stage.previous).card) :
    result.terminal = .overloaded :=
  result.outcome.terminal_overloaded_of_totalCapacity_lt_cardinality tooMany

/-- Pointwise bounds force this exact execution to the bounded terminal. -/
theorem terminal_bounded_of_bounded {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (bounded : forall label : spec.Label result.stage.previous,
      fibreCount capability result.stage.previous label <=
        spec.capacity result.stage.previous label) :
    result.terminal = .bounded :=
  result.outcome.terminal_bounded_of_bounded bounded

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT9 is total, exactly traced, polynomially bounded, and retains the
literal predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uItem, uLabel} Previous)
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
theorem run_deterministic (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .overloaded ∨ result.terminal = .bounded :=
  result.outcome.terminal_exhaustive

/-- Global excess forces the public reference run to overload. -/
theorem run_terminal_overloaded_of_totalCapacity_lt_cardinality
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (tooMany : totalCapacity capability previous <
      (capability.itemsAt previous).card) :
    (run spec capability previous).terminal = .overloaded :=
  (run spec capability previous).terminal_overloaded_of_totalCapacity_lt_cardinality
    tooMany

/-- Pointwise fibre bounds force the public reference run to be bounded. -/
theorem run_terminal_bounded_of_bounded
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (bounded : forall label : spec.Label previous,
      fibreCount capability previous label <= spec.capacity previous label) :
    (run spec capability previous).terminal = .bounded :=
  (run spec capability previous).terminal_bounded_of_bounded bounded

end Hypostructure.CT9
