import StructuralExhaustion.CT17.Execution
namespace StructuralExhaustion.CT17
namespace Outcome
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (o : Outcome F input port terminal) : OutcomeClaim o := by
  cases o with
  | scope c => exact c.unavailable | ct3 _ h => exact h | ct10 _ h => exact h
  | c5 c => exact c.closes | ct8 _ h => exact h | c1 c => exact c.closes
  | ct14 _ h => exact h
end Outcome
namespace ExecutionResult
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) : OutcomeClaim r.outcome := r.outcome.verified
theorem traceValid {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) : @Graph.ValidTrace F input r.trace :=
  ⟨r.terminal, r.path, rfl⟩
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
    ∃ r : ExecutionResult F input port, OutcomeClaim r.outcome ∧ @Graph.ValidTrace F input r.trace := by
  let r := runTraced F input plan port handoff
  exact ⟨r, r.verified, r.traceValid⟩
theorem outcome_exhaustive {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) :
    r.terminal = .scope ∨ r.terminal = .ct3 ∨ r.terminal = .ct10 ∨
    r.terminal = .c5 ∨ r.terminal = .ct8 ∨ r.terminal = .c1 ∨
    r.terminal = .ct14 := by
  cases r with
  | mk _ _ o => cases o with
    | scope _ => exact Or.inl rfl
    | ct3 _ _ => exact Or.inr (Or.inl rfl)
    | ct10 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
    | c5 _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | ct8 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | c1 _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | ct14 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
end StructuralExhaustion.CT17
