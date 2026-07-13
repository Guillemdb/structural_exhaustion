import StructuralExhaustion.CT2.Execution

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : Input capability ctx)

namespace RawOutcome

/-- Mathematical meaning of every CT2 outcome.  Closure outcomes are actual
minimality contradictions; residual outcomes expose their complete finite
evidence without mentioning a consumer tactic. -/
def Valid {terminal : Graph.Terminal} :
    RawOutcome capability ctx input terminal → Prop
  | .deletionC2 _ => False
  | .replacementC2 _ => False
  | .separating residual =>
      (∃ candidate : capability.replacements.Candidate input.seed.piece,
        ∃ context : capability.contexts.Context
          (capability.interfaces.interface input.seed.piece),
          sourceObservation capability ctx input context ≠
            replacementObservation capability ctx input candidate context) ∧
      (∀ candidate : capability.replacements.Candidate input.seed.piece,
        ¬ ContextEquivalent capability ctx input candidate)
  | .criticality _ =>
      ∀ _candidate : capability.replacements.Candidate input.seed.piece, False

theorem verified {terminal : Graph.Terminal}
    (outcome : RawOutcome capability ctx input terminal) : outcome.Valid := by
  cases outcome with
  | deletionC2 witness =>
      exact (C2Certificate.deletion witness).contradiction
  | replacementC2 witness =>
      exact (C2Certificate.replacement witness).contradiction
  | separating residual =>
      exact ⟨⟨residual.candidate, residual.separator.context,
        residual.separator.differs⟩,
        residual.replacementTable.noEquivalent⟩
  | criticality residual => exact residual.noCandidate

end RawOutcome

namespace ExecutionResult

theorem verified (result : ExecutionResult capability ctx input) :
    result.outcome.Valid :=
  result.outcome.verified

theorem traceValid (result : ExecutionResult capability ctx input) :
    Graph.ValidTrace capability ctx input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

/-- Extract the deletion witness carried by this exact execution result. -/
def deletionWitness_of_terminal_eq
    (result : ExecutionResult capability ctx input)
    (terminalEq : result.terminal = .deletionC2) :
    DeletionWitness capability ctx input := by
  cases result with
  | mk _terminal _path outcome =>
      cases outcome with
      | deletionC2 witness => exact witness
      | replacementC2 _ => simp at terminalEq
      | separating _ => simp at terminalEq
      | criticality _ => simp at terminalEq

end ExecutionResult

theorem run_verified :
    (run capability ctx input).outcome.Valid :=
  (run capability ctx input).verified

theorem run_trace_valid :
    Graph.ValidTrace capability ctx input (run capability ctx input).trace :=
  (run capability ctx input).traceValid

/-- The reference runner always returns one semantically valid typed terminal
with a kernel-checked trace. -/
theorem run_total :
    ∃ result : ExecutionResult capability ctx input,
      result.outcome.Valid ∧
      Graph.ValidTrace capability ctx input result.trace := by
  exact ⟨run capability ctx input,
    run_verified capability ctx input,
    run_trace_valid capability ctx input⟩

/-- Determinism follows from equality to the unique pure reference
computation. -/
theorem run_deterministic
    (left right : ExecutionResult capability ctx input)
    (leftIsRun : left = run capability ctx input)
    (rightIsRun : right = run capability ctx input) : left = right :=
  leftIsRun.trans rightIsRun.symm

theorem outcome_exhaustive (result : ExecutionResult capability ctx input) :
    result.terminal = .deletionC2 ∨
    result.terminal = .replacementC2 ∨
    result.terminal = .separating ∨
    result.terminal = .criticality := by
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | deletionC2 _ => exact Or.inl rfl
      | replacementC2 _ => exact Or.inr (Or.inl rfl)
      | separating _ => exact Or.inr (Or.inr (Or.inl rfl))
      | criticality _ => exact Or.inr (Or.inr (Or.inr rfl))

/-- Every separating result is backed by a complete proof that no legal
replacement is context-equivalent. -/
theorem separating_is_exhaustive
    (residual : SeparatingContextResidual capability ctx input) :
    ∀ candidate : capability.replacements.Candidate input.seed.piece,
      ¬ ContextEquivalent capability ctx input candidate :=
  residual.replacementTable.noEquivalent

/-- A criticality residual proves that the exact legal-candidate universe is
empty, not merely that one search heuristic failed. -/
theorem criticality_has_no_candidate
    (residual : CriticalityResidual capability ctx input) :
    ∀ _candidate : capability.replacements.Candidate input.seed.piece, False :=
  residual.noCandidate

end StructuralExhaustion.CT2
