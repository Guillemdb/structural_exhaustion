import StructuralExhaustion.CT17.Execution

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
variable (capability : Capability S)
variable (ctx : Core.BranchContext P)
variable (input : Input S capability ctx)

namespace RawOutcome

def Valid {terminal : Graph.Terminal} :
    RawOutcome S capability ctx input terminal → Prop
  | .incompatibility residual =>
      ¬ S.Compatible ctx residual.target residual.offset
  | .exhausted certificate =>
      ∀ position : S.Position input.scale,
        ¬ Survives S capability ctx input position
  | .survivors residual =>
      residual.enumeration.survivors =
        residual.first :: residual.remaining ∧
      ∀ position, position ∈ residual.enumeration.survivors ↔
        Survives S capability ctx input position
  | .targetHit certificate =>
      S.orbitValue ctx input.scale certificate.offset =
        S.targetValue certificate.target
  | .orbit residual =>
      residual.values = capability.offsets.orderedValues.map
        (S.orbitValue ctx input.scale) ∧
      OrbitAvoids S capability ctx input

theorem verified {terminal : Graph.Terminal}
    (outcome : RawOutcome S capability ctx input terminal) : outcome.Valid := by
  cases outcome with
  | incompatibility residual => exact residual.incompatible
  | exhausted certificate => exact certificate.exhausted
  | survivors residual =>
      exact ⟨residual.exact, fun position => ⟨
        residual.enumeration.sound position,
        residual.enumeration.complete position⟩⟩
  | targetHit certificate => exact certificate.equal
  | orbit residual => exact ⟨residual.valuesExact, residual.avoids⟩

end RawOutcome

namespace ExecutionResult

theorem verified (result : ExecutionResult S capability ctx input) :
    result.outcome.Valid := result.outcome.verified

theorem traceValid (result : ExecutionResult S capability ctx input) :
    @Graph.ValidTrace P S capability ctx input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

end ExecutionResult

theorem run_verified : (run S capability ctx input).outcome.Valid :=
  (run S capability ctx input).verified

theorem run_trace_valid :
    @Graph.ValidTrace P S capability ctx input
      (run S capability ctx input).trace :=
  (run S capability ctx input).traceValid

theorem run_total :
    ∃ result : ExecutionResult S capability ctx input,
      result.outcome.Valid ∧
      @Graph.ValidTrace P S capability ctx input result.trace :=
  ⟨run S capability ctx input,
    run_verified S capability ctx input,
    run_trace_valid S capability ctx input⟩

theorem run_deterministic
    (left right : ExecutionResult S capability ctx input)
    (leftIsRun : left = run S capability ctx input)
    (rightIsRun : right = run S capability ctx input) : left = right :=
  leftIsRun.trans rightIsRun.symm

theorem outcome_exhaustive (result : ExecutionResult S capability ctx input) :
    result.terminal = .incompatibility ∨
    result.terminal = .exhausted ∨
    result.terminal = .survivors ∨
    result.terminal = .targetHit ∨
    result.terminal = .orbit := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | incompatibility _ => exact Or.inl rfl
      | exhausted _ => exact Or.inr (Or.inl rfl)
      | survivors _ => exact Or.inr (Or.inr (Or.inl rfl))
      | targetHit _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | orbit _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem run_exhaustive :
    (run S capability ctx input).terminal = .incompatibility ∨
    (run S capability ctx input).terminal = .exhausted ∨
    (run S capability ctx input).terminal = .survivors ∨
    (run S capability ctx input).terminal = .targetHit ∨
    (run S capability ctx input).terminal = .orbit :=
  outcome_exhaustive S capability ctx input (run S capability ctx input)

theorem run_matches_reference :
    run S capability ctx input = runReference S capability ctx input := rfl

end StructuralExhaustion.CT17
