import StructuralExhaustion.CT1.Execution

namespace StructuralExhaustion.CT1

namespace Outcome

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal}
    (outcome : Outcome F input port terminal) : OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unavailable
  | c1 certificate => exact certificate.target
  | ct2 _ accepted => exact accepted
  | ct3 _ accepted => exact accepted
  | ct4 _ accepted => exact accepted
  | ct5 _ accepted => exact accepted
  | ct6 _ accepted => exact accepted
  | ct17 _ accepted => exact accepted

end Outcome

namespace ExecutionResult

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) :
    OutcomeClaim result.outcome :=
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

/-- Totality relative to the four supplied proof-producing node plans. -/
theorem run_total (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    ∃ result : ExecutionResult F input port,
      OutcomeClaim result.outcome ∧
        @Graph.ValidTrace F input result.trace := by
  let result := runTraced F input plan port handoff
  exact ⟨result, result.verified, result.traceValid⟩

theorem outcome_exhaustive {F : Framework} {input : Input F}
    {port : Port F input} (result : ExecutionResult F input port) :
    result.terminal = .scope ∨
    result.terminal = .c1 ∨
    result.terminal = .ct2 ∨
    result.terminal = .ct3 ∨
    result.terminal = .ct4 ∨
    result.terminal = .ct5 ∨
    result.terminal = .ct6 ∨
    result.terminal = .ct17 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | c1 _ => exact Or.inr (Or.inl rfl)
      | ct2 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
      | ct3 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct4 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | ct5 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | ct6 _ _ =>
          exact Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      | ct17 _ _ =>
          exact Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem c1_terminal_covered {F : Framework} {input : Input F}
    (certificate : C1Certificate F input) :
    Nonempty (RawOutcome F input .c1) :=
  ⟨.c1 certificate⟩

theorem c1_terminal_closes {F : Framework} {input : Input F}
    (certificate : C1Certificate F input) : F.ct2.Target input.G :=
  certificate.target

theorem ct2_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT2Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct2) :=
  ⟨.ct2 payload⟩

theorem ct3_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT3Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct3) :=
  ⟨.ct3 payload⟩

theorem ct4_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT4Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct4) :=
  ⟨.ct4 payload⟩

theorem ct5_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT5Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct5) :=
  ⟨.ct5 payload⟩

theorem ct6_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT6Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct6) :=
  ⟨.ct6 payload⟩

theorem ct17_terminal_covered {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT17Payload F input avoiding) :
    Nonempty (RawOutcome F input .ct17) :=
  ⟨.ct17 payload⟩

/-- The CT1→CT2 adapter preserves the ambient object definitionally. -/
theorem ct2_payload_same_ambient {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT2Payload F input avoiding) :
    payload.toInput.G = input.G := rfl

theorem ct3_payload_aligned {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT3Payload F input avoiding) :
    F.CT3Aligned input.G input.branch payload.toInput :=
  payload.aligned

theorem ct4_payload_aligned {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT4Payload F input avoiding) :
    F.CT4Aligned input.G input.branch payload.toInput :=
  payload.aligned

theorem ct5_payload_aligned {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT5Payload F input avoiding) :
    F.CT5Aligned input.G input.branch payload.toInput :=
  payload.aligned

end StructuralExhaustion.CT1
