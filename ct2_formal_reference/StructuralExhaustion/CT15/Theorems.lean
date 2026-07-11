import StructuralExhaustion.CT15.Execution
namespace StructuralExhaustion.CT15
namespace Outcome
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) : OutcomeClaim outcome := by
  cases outcome with
  | scope c => exact c.unavailable
  | ct3 _ h => exact h | ct7 _ h => exact h | ct16 _ h => exact h
  | c4 c => exact c.closes | ct4 _ h => exact h
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
    r.terminal = .scope ∨ r.terminal = .ct3 ∨ r.terminal = .ct7 ∨
    r.terminal = .ct16 ∨ r.terminal = .c4 ∨ r.terminal = .ct4 := by
  cases r with
  | mk _ _ o => cases o with
    | scope _ => exact Or.inl rfl
    | ct3 _ _ => exact Or.inr (Or.inl rfl)
    | ct7 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
    | ct16 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | c4 _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | ct4 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
end StructuralExhaustion.CT15
