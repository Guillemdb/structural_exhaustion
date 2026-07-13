import StructuralExhaustion.CT12.Execution

namespace StructuralExhaustion.CT12

universe uAmbient uBranch uState uPeeled uDemand uTier
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P)

namespace Outcome
def Valid {terminal : Graph.Terminal} : Outcome capability terminal → Prop
  | .exhausted _ => Nonempty (capability.State 0)
  | .demand _ => Nonempty capability.DemandResidual
  | .tier _ => Nonempty capability.TierResidual
theorem verified {terminal : Graph.Terminal}
    (outcome : Outcome capability terminal) : outcome.Valid := by
  cases outcome with
  | exhausted certificate => exact ⟨certificate.state⟩
  | demand residual => exact ⟨residual⟩
  | tier residual => exact ⟨residual⟩
end Outcome

namespace Graph.Edge
/-- Every back edge exposes the strict decrease that licensed recursion. -/
theorem loopBack_decreases (edge : Graph.Edge capability .decrease .saturation) :
    ∃ load next : Nat, next < load := by
  cases edge with
  | loopBack peeled nextState decreases =>
      exact ⟨_, _, decreases⟩
end Graph.Edge

namespace ExecutionResult
theorem verified {input : Input capability} (r : ExecutionResult capability input) :
    r.outcome.Valid := r.outcome.verified
theorem traceValid {input : Input capability} (r : ExecutionResult capability input) :
    Graph.ValidTrace capability r.trace := ⟨r.terminal, r.path, rfl⟩
end ExecutionResult

theorem run_verified (input : Input capability) : (run capability input).outcome.Valid :=
  (run capability input).verified
theorem run_trace_valid (input : Input capability) :
    Graph.ValidTrace capability (run capability input).trace :=
  (run capability input).traceValid
theorem run_iterations_bounded (input : Input capability) :
    (run capability input).iterations ≤ input.load :=
  (run capability input).iterations_le_load
theorem run_trace_bounded (input : Input capability) :
    (run capability input).trace.length ≤ 4 * input.load + 3 :=
  (run capability input).trace_length_le
theorem run_total (input : Input capability) :
    ∃ r : ExecutionResult capability input,
      r.outcome.Valid ∧ Graph.ValidTrace capability r.trace ∧
      r.iterations ≤ input.load ∧ r.trace.length ≤ 4 * input.load + 3 :=
  ⟨run capability input, run_verified capability input,
    run_trace_valid capability input, run_iterations_bounded capability input,
    run_trace_bounded capability input⟩
theorem run_deterministic {input : Input capability}
    (l r : ExecutionResult capability input)
    (hl : l = run capability input) (hr : r = run capability input) : l = r :=
  hl.trans hr.symm
theorem outcome_exhaustive {input : Input capability}
    (result : ExecutionResult capability input) :
    result.terminal = .exhausted ∨ result.terminal = .demand ∨
      result.terminal = .tier := by
  cases result with
  | mk _ _ outcome _ _ _ =>
      cases outcome with
      | exhausted _ => exact Or.inl rfl
      | demand _ => exact Or.inr (Or.inl rfl)
      | tier _ => exact Or.inr (Or.inr rfl)

end StructuralExhaustion.CT12
