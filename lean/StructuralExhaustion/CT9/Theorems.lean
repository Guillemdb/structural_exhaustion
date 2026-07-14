import StructuralExhaustion.CT9.Execution

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem uLabel
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
variable (input : Input capability)

namespace Outcome
def Valid {terminal} : Outcome capability input terminal → Prop
  | .overloaded residual => capability.capacity residual.label <
      fibreCount capability input residual.label
  | .bounded certificate => ∀ label,
      fibreCount capability input label ≤ capability.capacity label
theorem verified {terminal} (outcome : Outcome capability input terminal) :
    outcome.Valid := by
  cases outcome with
  | overloaded residual => exact residual.overloaded
  | bounded certificate => exact certificate.bounded
end Outcome

namespace ExecutionResult
theorem verified (result : ExecutionResult capability input) : result.outcome.Valid :=
  result.outcome.verified
theorem traceValid (result : ExecutionResult capability input) :
  Graph.ValidTrace capability input result.trace := ⟨result.terminal, result.path, rfl⟩

/-- Extract the overload residual carried by this exact execution result.
The terminal equality constructively rules out the bounded outcome. -/
def overloadResidual_of_terminal_eq
    (result : ExecutionResult capability input)
    (terminalEq : result.terminal = .overloaded) :
    OverloadResidual capability input := by
  cases result with
  | mk _terminal _path outcome =>
      cases outcome with
      | overloaded residual => exact residual
      | bounded _certificate => simp at terminalEq
end ExecutionResult

theorem run_verified : (run capability input).outcome.Valid :=
  (run capability input).verified
theorem run_trace_valid :
    Graph.ValidTrace capability input (run capability input).trace :=
  (run capability input).traceValid
theorem run_total : ∃ result : ExecutionResult capability input,
    result.outcome.Valid ∧ Graph.ValidTrace capability input result.trace :=
  ⟨run capability input, run_verified capability input, run_trace_valid capability input⟩
theorem run_deterministic (left right : ExecutionResult capability input)
    (hl : left = run capability input) (hr : right = run capability input) : left = right :=
  hl.trans hr.symm
theorem outcome_exhaustive (result : ExecutionResult capability input) :
    result.terminal = .overloaded ∨ result.terminal = .bounded := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | overloaded _ => exact Or.inl rfl
      | bounded _ => exact Or.inr rfl

/-- Global excess capacity forces the current reference run to terminate at
the overloaded branch. -/
theorem run_terminal_overloaded_of_totalCapacity_lt_cardinality
    (tooMany : totalCapacity capability < input.items.values.length) :
    (run capability input).terminal = .overloaded := by
  cases decision : analyze capability input with
  | overloaded residual =>
      simp [run, runReference, decision]
  | bounded certificate =>
      exact (certificate.false_of_totalCapacity_lt_cardinality tooMany).elim

/-- Global excess fixes the complete audit trace of the reference runner, not
only its terminal tag.  Applications therefore do not need to repeat the
case split on `analyze` to expose the overloaded path. -/
theorem run_trace_overloaded_of_totalCapacity_lt_cardinality
    (tooMany : totalCapacity capability < input.items.values.length) :
    (run capability input).trace =
      [.entry, .partition, .overload, .overloadedTerminal] := by
  cases decision : analyze capability input with
  | overloaded residual =>
      simp only [run]
      unfold runReference
      rw [decision]
      rfl
  | bounded certificate =>
      exact (certificate.false_of_totalCapacity_lt_cardinality tooMany).elim

/-- Pointwise fibre bounds force the actual reference run to the bounded
terminal.  This is the exact dual of the global-overload constructor. -/
theorem run_terminal_bounded_of_bounded
    (bounded : ∀ label,
      fibreCount capability input label ≤ capability.capacity label) :
    (run capability input).terminal = .bounded := by
  cases decision : analyze capability input with
  | overloaded residual =>
      exact (Nat.not_lt_of_ge (bounded residual.label)
        residual.overloaded).elim
  | bounded certificate =>
      simp [run, runReference, decision]

/-- Exact typed trace of the reference runner under pointwise fibre bounds. -/
theorem run_trace_bounded_of_bounded
    (bounded : ∀ label,
      fibreCount capability input label ≤ capability.capacity label) :
    (run capability input).trace =
      [.entry, .partition, .overload, .boundedTerminal] := by
  cases decision : analyze capability input with
  | overloaded residual =>
      exact (Nat.not_lt_of_ge (bounded residual.label)
        residual.overloaded).elim
  | bounded certificate =>
      simp only [run]
      unfold runReference
      rw [decision]
      rfl

/-- If the authored label map is injective on the exact active collection,
then every computed fibre has capacity at most one.  This is the reusable
capacity-one bridge used by representative-packing arguments: applications
prove only semantic injectivity, while CT9 owns the finite partition. -/
theorem fibreCount_le_one_of_label_injective_on_items
    (injectiveOnItems : ∀ {first second : capability.Item},
      first ∈ input.items.values → second ∈ input.items.values →
      capability.label first = capability.label second → first = second) :
    ∀ label, fibreCount capability input label ≤ 1 := by
  letI : DecidableEq capability.Label := capability.labels.decEq
  letI : DecidableEq capability.Item := input.items.decEq
  intro label
  let values := fibre capability input label
  have valuesNodup : values.Nodup := by
    exact input.items.nodup.filter _
  change values.length ≤ 1
  rw [← values.toFinset_card_of_nodup valuesNodup]
  rw [Finset.card_le_one_iff]
  intro first second firstMem secondMem
  have firstFiltered :
      first ∈ input.items.values ∧ capability.label first = label := by
    simpa [values, fibre] using firstMem
  have secondFiltered :
      second ∈ input.items.values ∧ capability.label second = label := by
    simpa [values, fibre] using secondMem
  exact injectiveOnItems firstFiltered.1 secondFiltered.1
    (firstFiltered.2.trans secondFiltered.2.symm)

/-- A semantic proof that no active item carries one label turns that exact
computed fibre into the zero-capacity certificate. -/
theorem fibreCount_eq_zero_of_label_absent
    (label : capability.Label)
    (absent : ∀ item ∈ input.items.values,
      capability.label item ≠ label) :
    fibreCount capability input label = 0 := by
  letI : DecidableEq capability.Label := capability.labels.decEq
  unfold fibreCount fibre
  rw [List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro item itemMem
  simpa using absent item itemMem

/-- Pointwise bounds can be consumed directly as a global cardinality bound,
without manufacturing a search result or re-running `analyze`. -/
theorem cardinality_le_totalCapacity_of_bounded
    (bounded : ∀ label,
      fibreCount capability input label ≤ capability.capacity label) :
    input.items.values.length ≤ totalCapacity capability :=
  (show BoundedCertificate capability input from ⟨bounded⟩).cardinality_le_totalCapacity

/-- Capacity-one specialization of the generic global cardinality theorem. -/
theorem cardinality_le_totalCapacity_of_label_injective_on_items
    (capacityOne : ∀ label : capability.Label,
      capability.capacity label = 1)
    (injectiveOnItems : ∀ {first second : capability.Item},
      first ∈ input.items.values → second ∈ input.items.values →
      capability.label first = capability.label second → first = second) :
    input.items.values.length ≤ totalCapacity capability := by
  apply cardinality_le_totalCapacity_of_bounded capability input
  intro label
  rw [capacityOne label]
  exact fibreCount_le_one_of_label_injective_on_items capability input
    injectiveOnItems label

/-- Obtain the typed overload evidence selected by the same exact analysis
used by `run`, without re-casing the search in an application. -/
def runOverloadResidualOfTotalCapacityLtCardinality
    (tooMany : totalCapacity capability < input.items.values.length) :
    OverloadResidual capability input :=
  ExecutionResult.overloadResidual_of_terminal_eq capability input
    (run capability input)
    (run_terminal_overloaded_of_totalCapacity_lt_cardinality
      capability input tooMany)

/-- Run the reference analysis once conceptually and extract two distinct
active items in its overloaded fibre.  The all-label capacity-one hypothesis
is convenient for applications whose labels are simple pigeonhole boxes; the
selected label and both items remain determined by CT9's declared search
order. -/
def runSameLabelPairOfTotalCapacityLtCardinality
    (tooMany : totalCapacity capability < input.items.values.length)
    (capacityOne : ∀ label : capability.Label,
      capability.capacity label = 1) :
    SameLabelPair capability input
      (runOverloadResidualOfTotalCapacityLtCardinality capability input
        tooMany).label :=
  let residual :=
    runOverloadResidualOfTotalCapacityLtCardinality capability input tooMany
  residual.sameLabelPairOfCapacityOne (capacityOne residual.label)

/-- Exact reference-run package for a cardinality-forced overload.

The residual accessor is obtained from this exact run using `terminal_eq`, so
consumers cannot accidentally combine a valid overload proof with a different
execution. -/
structure OverloadedRun where
  terminal_eq : (run capability input).terminal = .overloaded
  trace_eq : (run capability input).trace =
    [.entry, .partition, .overload, .overloadedTerminal]

namespace OverloadedRun

/-- The reference execution certified by this package. -/
def execution (_bundle : OverloadedRun capability input) :
    ExecutionResult capability input :=
  run capability input

/-- The overload residual carried by the certified reference execution. -/
def residual (bundle : OverloadedRun capability input) :
    OverloadResidual capability input :=
  ExecutionResult.overloadResidual_of_terminal_eq capability input
    bundle.execution bundle.terminal_eq

/-- Extract two distinct same-label items from the exact selected fibre when
the selected label has capacity one. -/
def sameLabelPairOfCapacityOne (bundle : OverloadedRun capability input)
    (capacityOne : capability.capacity bundle.residual.label = 1) :
    SameLabelPair capability input bundle.residual.label :=
  bundle.residual.sameLabelPairOfCapacityOne capacityOne

end OverloadedRun

/-- Force and package the overloaded reference branch from global excess. -/
def runOverloadedOfTotalCapacityLtCardinality
    (tooMany : totalCapacity capability < input.items.values.length) :
    OverloadedRun capability input where
  terminal_eq :=
    run_terminal_overloaded_of_totalCapacity_lt_cardinality capability input
      tooMany
  trace_eq :=
    run_trace_overloaded_of_totalCapacity_lt_cardinality capability input
      tooMany

/-- Exact reference-run package for a pointwise bounded partition. -/
structure BoundedRun where
  terminal_eq : (run capability input).terminal = .bounded
  trace_eq : (run capability input).trace =
    [.entry, .partition, .overload, .boundedTerminal]

namespace BoundedRun

def execution (_bundle : BoundedRun capability input) :
    ExecutionResult capability input :=
  run capability input

end BoundedRun

/-- Force and package the bounded reference branch from exact pointwise
capacity bounds. -/
def runBoundedOfBounded
    (bounded : ∀ label,
      fibreCount capability input label ≤ capability.capacity label) :
    BoundedRun capability input where
  terminal_eq := run_terminal_bounded_of_bounded capability input bounded
  trace_eq := run_trace_bounded_of_bounded capability input bounded

/-- Force the exact bounded CT9 branch from semantic injectivity of a
capacity-one labelling on the supplied active collection. -/
def runBoundedOfLabelInjectiveOnItems
    (capacityOne : ∀ label : capability.Label,
      capability.capacity label = 1)
    (injectiveOnItems : ∀ {first second : capability.Item},
      first ∈ input.items.values → second ∈ input.items.values →
      capability.label first = capability.label second → first = second) :
    BoundedRun capability input :=
  runBoundedOfBounded capability input fun label => by
    rw [capacityOne label]
    exact fibreCount_le_one_of_label_injective_on_items capability input
      injectiveOnItems label

end StructuralExhaustion.CT9
