import StructuralExhaustion.CT8.Execution
namespace StructuralExhaustion.CT8
namespace Outcome
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unavailable
  | ct10 _ accepted => exact accepted
  | c5 certificate => exact certificate.closes
  | c2 certificate => exact certificate.closes
  | ct3 _ accepted => exact accepted
  | ct7 _ accepted => exact accepted
end Outcome
namespace ExecutionResult
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : OutcomeClaim result.outcome :=
  result.outcome.verified
theorem traceValid {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : @Graph.ValidTrace F input result.trace :=
  ⟨result.terminal, result.path, rfl⟩
end ExecutionResult
theorem run_verified (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    OutcomeClaim (runTraced F input plan port handoff).outcome :=
  (runTraced F input plan port handoff).verified
theorem run_trace_valid (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    @Graph.ValidTrace F input (runTraced F input plan port handoff).trace :=
  (runTraced F input plan port handoff).traceValid
theorem run_total (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    ∃ result : ExecutionResult F input port,
      OutcomeClaim result.outcome ∧ @Graph.ValidTrace F input result.trace := by
  let result := runTraced F input plan port handoff
  exact ⟨result, result.verified, result.traceValid⟩
theorem outcome_exhaustive {F : Framework} {input : Input F}
    {port : Port F input} (result : ExecutionResult F input port) :
    result.terminal = .scope ∨ result.terminal = .ct10 ∨
    result.terminal = .c5 ∨ result.terminal = .c2 ∨
    result.terminal = .ct3 ∨ result.terminal = .ct7 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | ct10 _ _ => exact Or.inr (Or.inl rfl)
      | c5 _ => exact Or.inr (Or.inr (Or.inl rfl))
      | c2 _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct3 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | ct7 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
end StructuralExhaustion.CT8
