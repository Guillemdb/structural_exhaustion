import StructuralExhaustion.CT2.Execution

namespace StructuralExhaustion.CT2

namespace Outcome

/-- Every indexed outcome establishes exactly the claim advertised by its
terminal constructor. -/
theorem verified {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal}
    (outcome : Outcome F input port terminal) : OutcomeClaim outcome := by
  cases outcome with
  | scope candidate => exact candidate.unbounded
  | deletionC2 witness =>
      exact (C2Certificate.ofDeletion witness).contradiction
  | contextCT3 _ accepted => exact accepted
  | replacementC2 state certificate =>
      exact (C2Certificate.ofReplacement state certificate).contradiction
  | criticalityCT10 _ accepted => exact accepted
  | responseCT3 _ accepted => exact accepted

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

/-- Aggregate soundness for full execution. -/
theorem run_verified (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    OutcomeClaim (runTraced F input plan port handoff).outcome :=
  (runTraced F input plan port handoff).verified

/-- The erased trace always has an evidence-carrying semantic path behind it. -/
theorem run_trace_valid (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    @Graph.ValidTrace F input
      (runTraced F input plan port handoff).trace :=
  ExecutionResult.traceValid (runTraced F input plan port handoff)

/-- Totality relative to the explicitly supplied proof-producing node plans. -/
theorem run_total (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    ∃ result : ExecutionResult F input port,
      OutcomeClaim result.outcome ∧
        @Graph.ValidTrace F input result.trace := by
  let result := runTraced F input plan port handoff
  exact ⟨result, result.verified, ExecutionResult.traceValid result⟩

/-- The six indexed terminals are exhaustive for a completed execution. -/
theorem outcome_exhaustive {F : Framework} {input : Input F}
    {port : Port F input} (result : ExecutionResult F input port) :
    result.terminal = .scope ∨
    result.terminal = .deletionC2 ∨
    result.terminal = .contextCT3 ∨
    result.terminal = .replacementC2 ∨
    result.terminal = .criticalityCT10 ∨
    result.terminal = .responseCT3 := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | scope _ => exact Or.inl rfl
      | deletionC2 _ => exact Or.inr (Or.inl rfl)
      | contextCT3 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
      | replacementC2 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | criticalityCT10 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | responseCT3 _ _ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- Parametric coverage of the deletion C2 terminal.  The index itself records
that this evidence cannot be confused with replacement closure. -/
theorem deletion_terminal_covered {F : Framework} {input : Input F}
    (witness : DeletionWitness F input) :
    Nonempty (RawOutcome F input .deletionC2) :=
  ⟨.deletionC2 witness⟩

/-- Parametric coverage of the replacement C2 terminal. -/
theorem replacement_terminal_covered {F : Framework} {input : Input F}
    (state : CandidateState F input)
    (certificate : CandidateContextCertificate F input state) :
    Nonempty (RawOutcome F input .replacementC2) :=
  ⟨.replacementC2 state certificate⟩

theorem deletion_terminal_closes {F : Framework} {input : Input F}
    (witness : DeletionWitness F input) : False :=
  (C2Certificate.ofDeletion witness).contradiction

theorem replacement_terminal_closes {F : Framework} {input : Input F}
    (state : CandidateState F input)
    (certificate : CandidateContextCertificate F input state) : False :=
  (C2Certificate.ofReplacement state certificate).contradiction

theorem context_ct3_payload_aligned {F : Framework} {input : Input F}
    {state : CandidateState F input}
    (payload : ContextCT3Payload F input state) :
    F.ContextCT3Aligned input.G input.X state.candidate.replacement
      payload.residual.outside payload.downstream :=
  payload.aligned

theorem response_ct3_payload_aligned {F : Framework} {input : Input F}
    {survivor : SurvivorState F input}
    (payload : ResponseCT3Payload F input survivor) :
    F.ResponseCT3Aligned input.G input.X payload.datum payload.downstream :=
  payload.aligned

end StructuralExhaustion.CT2
