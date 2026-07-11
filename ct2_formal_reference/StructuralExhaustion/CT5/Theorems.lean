import StructuralExhaustion.CT5.Execution

namespace StructuralExhaustion.CT5

namespace Outcome

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unavailable
  | ct11 _ accepted => exact accepted
  | c4 certificate => exact certificate.closes
  | ct4 _ accepted => exact accepted
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
    result.terminal = .scope ∨ result.terminal = .ct11 ∨
    result.terminal = .c4 ∨ result.terminal = .ct4 ∨
    result.terminal = .ct14 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | ct11 _ _ => exact Or.inr (Or.inl rfl)
      | c4 _ => exact Or.inr (Or.inr (Or.inl rfl))
      | ct4 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct14 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem c4_terminal_closes {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (certificate : C4Certificate F input summation) :
    F.ct4.C4Claim input.G input.branch := certificate.closes

theorem ct4_payload_same_ambient {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT4Payload F input summation) :
    payload.toInput.G = input.G := rfl

theorem ct4_payload_same_branch {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT4Payload F input summation) :
    payload.toInput.branch = input.branch := rfl

theorem ct11_terminal_covered {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    (payload : CT11Payload F input locality) :
    Nonempty (RawOutcome F input .ct11) := ⟨.ct11 payload⟩

theorem ct4_terminal_covered {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT4Payload F input summation) :
    Nonempty (RawOutcome F input .ct4) := ⟨.ct4 payload⟩

theorem ct14_terminal_covered {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT14Payload F input summation) :
    Nonempty (RawOutcome F input .ct14) := ⟨.ct14 payload⟩

end StructuralExhaustion.CT5
