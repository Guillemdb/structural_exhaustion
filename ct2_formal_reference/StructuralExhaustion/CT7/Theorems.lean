import StructuralExhaustion.CT7.Execution

namespace StructuralExhaustion.CT7

namespace Outcome
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unavailable
  | c1 certificate => exact certificate.closes
  | c3 certificate => exact certificate.closes
  | ct3 _ accepted => exact accepted
  | ct12 _ accepted => exact accepted
  | c2 certificate => exact certificate.closes
  | ct10 _ accepted => exact accepted
  | ct16 _ accepted => exact accepted
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
    result.terminal = .scope ∨ result.terminal = .c1 ∨
    result.terminal = .c3 ∨ result.terminal = .ct3 ∨
    result.terminal = .ct12 ∨ result.terminal = .c2 ∨
    result.terminal = .ct10 ∨ result.terminal = .ct16 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | c1 _ => exact Or.inr (Or.inl rfl)
      | c3 _ => exact Or.inr (Or.inr (Or.inl rfl))
      | ct3 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct12 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | c2 _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | ct10 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      | ct16 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem ct3_adapter_exact {F : Framework} {input : Input F}
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    {defect : DefectState F input unrealized}
    (payload : CT3Payload F input defect) : payload.toInput = payload.downstream := rfl

end StructuralExhaustion.CT7
