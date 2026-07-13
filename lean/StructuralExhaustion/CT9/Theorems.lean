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

end StructuralExhaustion.CT9
