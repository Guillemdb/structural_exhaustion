import StructuralExhaustion.CT4.Execution

namespace StructuralExhaustion.CT4

namespace Outcome

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unavailable
  | ct13 _ accepted => exact accepted
  | ct9 _ accepted => exact accepted
  | c4 certificate => exact certificate.closes
  | ct14 _ accepted => exact accepted

end Outcome

namespace ExecutionResult

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : OutcomeClaim result.outcome :=
  result.outcome.verified

theorem traceValid {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) :
    @Graph.ValidTrace F input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

end ExecutionResult

theorem run_verified (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    OutcomeClaim (runTraced F input plan port handoff).outcome :=
  (runTraced F input plan port handoff).verified

theorem run_trace_valid (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    @Graph.ValidTrace F input (runTraced F input plan port handoff).trace :=
  (runTraced F input plan port handoff).traceValid

theorem run_total (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    ∃ result : ExecutionResult F input port,
      OutcomeClaim result.outcome ∧ @Graph.ValidTrace F input result.trace := by
  let result := runTraced F input plan port handoff
  exact ⟨result, result.verified, result.traceValid⟩

theorem outcome_exhaustive {F : Framework} {input : Input F}
    {port : Port F input} (result : ExecutionResult F input port) :
    result.terminal = .scope ∨ result.terminal = .ct13 ∨
    result.terminal = .ct9 ∨ result.terminal = .c4 ∨
    result.terminal = .ct14 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | ct13 _ _ => exact Or.inr (Or.inl rfl)
      | ct9 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
      | c4 _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct14 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem c4_terminal_closes {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    {bounded : BoundedFibreState F input total}
    (certificate : C4Certificate F input bounded) :
    F.C4Claim input.G input.branch := certificate.closes

theorem ct13_terminal_covered {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    (payload : CT13Payload F input assignment) :
    Nonempty (RawOutcome F input .ct13) := ⟨.ct13 payload⟩

theorem ct9_terminal_covered {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (payload : CT9Payload F input total) :
    Nonempty (RawOutcome F input .ct9) := ⟨.ct9 payload⟩

theorem ct14_terminal_covered {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    {bounded : BoundedFibreState F input total}
    (payload : CT14Payload F input bounded) :
    Nonempty (RawOutcome F input .ct14) := ⟨.ct14 payload⟩

end StructuralExhaustion.CT4
