import StructuralExhaustion.CT5.Execution

namespace StructuralExhaustion.CT5

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

namespace RawOutcome
def Valid {terminal} : RawOutcome S capability input terminal → Prop
  | .deficit residual => DeficitAt S input residual.site
  | .c4 certificate =>
      capability.capacity input < capability.required input
  | .charge residual => residual.ledger.total ≤ capability.capacity input
  | .aggregate residual =>
      capability.required input ≤ capability.capacity input ∧
      capability.capacity input < residual.ledger.total

theorem verified {terminal} (outcome : RawOutcome S capability input terminal) :
    outcome.Valid := by
  cases outcome with
  | deficit residual => exact ⟨residual.active, residual.noWitness⟩
  | c4 certificate => exact certificate.capacity_lt_required
  | charge residual => exact residual.total_le_capacity
  | aggregate residual => exact ⟨residual.required_le_capacity,
      residual.capacity_lt_total⟩
end RawOutcome

namespace ExecutionResult
theorem verified (result : ExecutionResult S capability input) :
    result.outcome.Valid := result.outcome.verified
theorem traceValid (result : ExecutionResult S capability input) :
    Graph.ValidTrace S capability input result.trace :=
  ⟨result.terminal, result.path, rfl⟩
end ExecutionResult

theorem run_verified : (run S capability input).outcome.Valid :=
  (run S capability input).verified
theorem run_trace_valid :
    Graph.ValidTrace S capability input (run S capability input).trace :=
  (run S capability input).traceValid
theorem run_total : ∃ result : ExecutionResult S capability input,
    result.outcome.Valid ∧ Graph.ValidTrace S capability input result.trace :=
  ⟨run S capability input, run_verified S capability input,
    run_trace_valid S capability input⟩
theorem run_deterministic (left right : ExecutionResult S capability input)
    (hl : left = run S capability input) (hr : right = run S capability input) :
    left = right := hl.trans hr.symm

theorem outcome_exhaustive (result : ExecutionResult S capability input) :
    result.terminal = .deficit ∨
      result.terminal = .c4 ∨
      result.terminal = .charge ∨
      result.terminal = .aggregate := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | deficit _ => exact Or.inl rfl
      | c4 _ => exact Or.inr (Or.inl rfl)
      | charge _ => exact Or.inr (Or.inr (Or.inl rfl))
      | aggregate _ => exact Or.inr (Or.inr (Or.inr rfl))

end StructuralExhaustion.CT5
