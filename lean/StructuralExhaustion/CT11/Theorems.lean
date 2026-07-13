import StructuralExhaustion.CT11.Execution

namespace StructuralExhaustion.CT11

universe uAmbient uBranch uCell
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uCell} P)
variable (input : Input capability)

namespace Outcome
def Valid {t} : Outcome capability input t → Prop
  | .gap r => r.cell ∈ input.cells.values ∧
      ¬ capability.Admissible input.context r.cell
  | .localized r => r.cell ∈ input.cells.values ∧
      capability.Admissible input.context r.cell ∧
      capability.localBudget input.context r.cell < 0
theorem verified {t} (o : Outcome capability input t) : o.Valid := by
  cases o with
  | gap r => exact ⟨r.member, r.inadmissible⟩
  | localized r => exact ⟨r.member, r.admissible.admissible r.cell r.member, r.negative⟩
end Outcome

namespace ExecutionResult
theorem verified (r : ExecutionResult capability input) : r.outcome.Valid := r.outcome.verified
theorem traceValid (r : ExecutionResult capability input) :
    Graph.ValidTrace capability input r.trace := ⟨r.terminal, r.path, rfl⟩
end ExecutionResult

theorem run_verified : (run capability input).outcome.Valid := (run capability input).verified
theorem run_trace_valid : Graph.ValidTrace capability input (run capability input).trace :=
  (run capability input).traceValid
theorem run_total : ∃ r : ExecutionResult capability input,
    r.outcome.Valid ∧ Graph.ValidTrace capability input r.trace :=
  ⟨run capability input, run_verified capability input, run_trace_valid capability input⟩
theorem run_deterministic (l r : ExecutionResult capability input)
    (hl : l = run capability input) (hr : r = run capability input) : l = r :=
  hl.trans hr.symm
theorem outcome_exhaustive (result : ExecutionResult capability input) :
    result.terminal = .gap ∨ result.terminal = .localized := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | gap _ => exact Or.inl rfl
      | localized _ => exact Or.inr rfl

end StructuralExhaustion.CT11
