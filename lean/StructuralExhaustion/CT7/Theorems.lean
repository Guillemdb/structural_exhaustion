import StructuralExhaustion.CT7.Execution

namespace StructuralExhaustion.CT7

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (ctx : Core.BranchContext P) (input : Input S ctx)
namespace RawOutcome
def Valid {terminal} : RawOutcome S capability ctx input terminal → Prop
  | .realization certificate => S.Realizes ctx input.left certificate.context
  | .distinguishing residual =>
      (∀ context, ¬ S.Realizes ctx input.left context) ∧
      S.response ctx input.left residual.context ≠
        S.response ctx input.right residual.context
  | .neutral certificate =>
      (∀ context, ¬ S.Realizes ctx input.left context) ∧
      ∀ context, S.response ctx input.left context = S.response ctx input.right context
theorem verified {terminal} (outcome : RawOutcome S capability ctx input terminal) :
    outcome.Valid := by
  cases outcome with
  | realization certificate => exact certificate.realizes
  | distinguishing residual => exact ⟨residual.unrealized.noRealization,
      residual.differs⟩
  | neutral certificate => exact ⟨certificate.unrealized.noRealization,
      certificate.allEqual⟩
end RawOutcome
namespace ExecutionResult
theorem verified (result : ExecutionResult S capability ctx input) :
    result.outcome.Valid := result.outcome.verified
theorem traceValid (result : ExecutionResult S capability ctx input) :
    Graph.ValidTrace S capability ctx input result.trace :=
  ⟨result.terminal, result.path, rfl⟩
end ExecutionResult
theorem run_verified : (run S capability ctx input).outcome.Valid :=
  (run S capability ctx input).verified
theorem run_trace_valid :
    Graph.ValidTrace S capability ctx input (run S capability ctx input).trace :=
  (run S capability ctx input).traceValid
theorem run_total : ∃ result : ExecutionResult S capability ctx input,
    result.outcome.Valid ∧ Graph.ValidTrace S capability ctx input result.trace :=
  ⟨run S capability ctx input, run_verified S capability ctx input,
    run_trace_valid S capability ctx input⟩
theorem run_deterministic (left right : ExecutionResult S capability ctx input)
    (hl : left = run S capability ctx input) (hr : right = run S capability ctx input) :
    left = right := hl.trans hr.symm

theorem outcome_exhaustive (result : ExecutionResult S capability ctx input) :
    result.terminal = .realization ∨
      result.terminal = .distinguishing ∨
      result.terminal = .neutral := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | realization _ => exact Or.inl rfl
      | distinguishing _ => exact Or.inr (Or.inl rfl)
      | neutral _ => exact Or.inr (Or.inr rfl)

end StructuralExhaustion.CT7
