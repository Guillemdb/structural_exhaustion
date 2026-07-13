import StructuralExhaustion.CT14.Execution

namespace StructuralExhaustion.CT14

def RawOutcome.Valid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {terminal} :
    RawOutcome C ctx terminal → Prop
  | .unbounded residual => C.memberCapacity ctx residual.member = none
  | .missingLabel residual => C.memberLabel ctx residual.member = none
  | .aggregate certificate => certificate.upper < certificate.lower
  | .capacity residual => residual.lower ≤ residual.upper

theorem RawOutcome.verified {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {terminal}
    (outcome : RawOutcome C ctx terminal) : outcome.Valid := by
  cases outcome with
  | unbounded residual => exact residual.missing
  | missingLabel residual => exact residual.missing
  | aggregate certificate => exact certificate.exceeds
  | capacity residual => exact residual.within

theorem ExecutionResult.traceValid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (result : ExecutionResult C ctx) :
    @Graph.ValidTrace P C ctx result.trace :=
  ⟨result.terminal, result.path, rfl⟩

theorem run_verified {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    (run C ctx input).outcome.Valid :=
  (run C ctx input).outcome.verified

theorem run_trace_valid {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    @Graph.ValidTrace P C ctx (run C ctx input).trace :=
  (run C ctx input).traceValid

theorem run_total {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    ∃ result : ExecutionResult C ctx,
      result.outcome.Valid ∧ @Graph.ValidTrace P C ctx result.trace :=
  ⟨run C ctx input, run_verified C ctx input, run_trace_valid C ctx input⟩

theorem run_deterministic {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx)
    (left right : ExecutionResult C ctx)
    (leftIsRun : left = run C ctx input)
    (rightIsRun : right = run C ctx input) : left = right :=
  leftIsRun.trans rightIsRun.symm

theorem outcome_exhaustive {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (result : ExecutionResult C ctx) :
    result.terminal = .unbounded ∨
      result.terminal = .missingLabel ∨
      result.terminal = .aggregate ∨
      result.terminal = .capacity := by
  cases result with
  | mk _ _ outcome =>
    cases outcome with
    | unbounded _ => exact Or.inl rfl
    | missingLabel _ => exact Or.inr (Or.inl rfl)
    | aggregate _ => exact Or.inr (Or.inr (Or.inl rfl))
    | capacity _ => exact Or.inr (Or.inr (Or.inr rfl))

end StructuralExhaustion.CT14
