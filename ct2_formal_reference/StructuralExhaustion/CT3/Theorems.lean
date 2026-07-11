import StructuralExhaustion.CT3.Execution

namespace StructuralExhaustion.CT3

namespace Outcome

theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} (outcome : Outcome F input port terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.infiniteIndex
  | c2 certificate => exact certificate.witness.closes
  | c3 certificate => exact certificate.closes
  | ct7 _ accepted => exact accepted
  | ct12 _ accepted => exact accepted
  | c5 certificate => exact certificate.closes
  | ct8 _ accepted => exact accepted

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
    result.terminal = .scope ∨ result.terminal = .c2 ∨
    result.terminal = .c3 ∨ result.terminal = .ct7 ∨
    result.terminal = .ct12 ∨ result.terminal = .c5 ∨
    result.terminal = .ct8 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | c2 _ => exact Or.inr (Or.inl rfl)
      | c3 _ => exact Or.inr (Or.inr (Or.inl rfl))
      | ct7 _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | ct12 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | c5 _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | ct8 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem c2_terminal_closes {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    (certificate : C2Certificate F input equivalence) :
    F.C2Claim input.G input.branch := certificate.witness.closes

theorem c3_terminal_closes {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (certificate : C3Certificate F input state) :
    F.C3Claim input.G input.branch := certificate.closes

theorem c5_terminal_closes {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    {persistent : PersistentState F input state}
    (certificate : C5Certificate F input persistent) :
    F.C5Claim input.G input.branch := certificate.closes

theorem ct7_terminal_covered {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (payload : CT7Payload F input state) :
    Nonempty (RawOutcome F input .ct7) := ⟨.ct7 payload⟩

theorem ct12_terminal_covered {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (payload : CT12Payload F input state) :
    Nonempty (RawOutcome F input .ct12) := ⟨.ct12 payload⟩

theorem ct8_terminal_covered {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    {persistent : PersistentState F input state}
    (payload : CT8Payload F input persistent) :
    Nonempty (RawOutcome F input .ct8) := ⟨.ct8 payload⟩

end StructuralExhaustion.CT3
