import StructuralExhaustion.CT8.Execution

namespace StructuralExhaustion.CT8

universe uAmbient uBranch uState uType uResponseContext
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)
variable (ctx : Core.BranchContext P)
variable (input : Input capability ctx)
namespace Outcome
def Valid {t} : Outcome capability ctx input t → Prop
  | .noRepetition c => OrderedRepeatedPair capability input.sequence → False
  | .removal r => ResponsesEqual capability ctx input r.pair ∧
      r.smaller = input.remove r.pair.first r.pair.second
  | .separation r => capability.response r.pair.first r.separator.context ≠
      capability.response r.pair.second r.separator.context
theorem verified {t} (o : Outcome capability ctx input t) : o.Valid := by
  cases o with
  | noRepetition c => exact c.absent
  | removal r => exact ⟨r.responsesEqual, r.exact⟩
  | separation r => exact r.separator.differs
end Outcome
namespace ExecutionResult
theorem verified (r : ExecutionResult capability ctx input) : r.outcome.Valid := r.outcome.verified
theorem traceValid (r : ExecutionResult capability ctx input) :
    Graph.ValidTrace capability ctx input r.trace := ⟨r.terminal, r.path, rfl⟩
end ExecutionResult
theorem run_verified : (run capability ctx input).outcome.Valid :=
  (run capability ctx input).verified
theorem run_trace_valid : Graph.ValidTrace capability ctx input
    (run capability ctx input).trace := (run capability ctx input).traceValid
theorem run_total : ∃ r : ExecutionResult capability ctx input,
    r.outcome.Valid ∧ Graph.ValidTrace capability ctx input r.trace :=
  ⟨run capability ctx input, run_verified capability ctx input,
    run_trace_valid capability ctx input⟩
theorem run_deterministic (l r : ExecutionResult capability ctx input)
    (hl : l = run capability ctx input) (hr : r = run capability ctx input) : l = r :=
  hl.trans hr.symm
theorem outcome_exhaustive (result : ExecutionResult capability ctx input) :
    result.terminal = .noRepetition ∨ result.terminal = .removal ∨
      result.terminal = .separation := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | noRepetition _ => exact Or.inl rfl
      | removal _ => exact Or.inr (Or.inl rfl)
      | separation _ => exact Or.inr (Or.inr rfl)
end StructuralExhaustion.CT8
