import StructuralExhaustion.CT4.Execution

namespace StructuralExhaustion.CT4

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)
namespace RawOutcome
def Valid {terminal} : RawOutcome S capability input terminal → Prop
  | .missing residual => MissingAt S input residual.demand
  | .overload residual =>
      Overloaded S capability input residual.total.assignment residual.payer
  | .c4 _ => totalCapacity S capability input < capability.required input
  | .capacity _ => capability.required input ≤ totalCapacity S capability input
theorem verified {terminal} (outcome : RawOutcome S capability input terminal) :
    outcome.Valid := by
  cases outcome with
  | missing residual => exact residual.noEligible
  | overload residual => exact residual.overloaded
  | c4 certificate => exact certificate.capacity_lt_required
  | capacity residual => exact residual.required_le_capacity
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
    result.terminal = .missing ∨
      result.terminal = .overload ∨
      result.terminal = .c4 ∨
      result.terminal = .capacity := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | missing _ => exact Or.inl rfl
      | overload _ => exact Or.inr (Or.inl rfl)
      | c4 _ => exact Or.inr (Or.inr (Or.inl rfl))
      | capacity _ => exact Or.inr (Or.inr (Or.inr rfl))

end StructuralExhaustion.CT4
