import StructuralExhaustion.CT13.Execution
namespace StructuralExhaustion.CT13
def RawOutcome.Valid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {t} : RawOutcome C ctx t → Prop
  | .tierOne r => C.Eligible ctx r.payer
  | .overlap r => r.left ≠ r.right ∧ C.resource ctx r.left = C.resource ctx r.right
  | .deficit r => r.state.capacity < C.demand ctx
  | .reconciled c => C.demand ctx ≤ c.state.capacity
theorem RawOutcome.verified {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {t} (o : RawOutcome C ctx t) : o.Valid := by
  cases o with
  | tierOne r => exact r.eligible | overlap r => exact ⟨r.different, r.sameResource⟩
  | deficit r => exact r.deficit | reconciled c => exact c.covers
theorem ExecutionResult.traceValid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (r : ExecutionResult C ctx) :
    @Graph.ValidTrace P C ctx r.trace := ⟨r.terminal, r.path, rfl⟩
theorem run_verified {P : Core.Problem} (C : Capability P) (ctx)
    (input : Input C ctx) : (run C ctx input).outcome.Valid :=
  (run C ctx input).outcome.verified
theorem run_trace_valid {P : Core.Problem} (C : Capability P) (ctx)
    (input : Input C ctx) : @Graph.ValidTrace P C ctx (run C ctx input).trace :=
  (run C ctx input).traceValid
theorem run_total {P : Core.Problem} (C : Capability P) (ctx)
    (input : Input C ctx) : ∃ r : ExecutionResult C ctx,
      r.outcome.Valid ∧ @Graph.ValidTrace P C ctx r.trace :=
  ⟨run C ctx input, run_verified C ctx input, run_trace_valid C ctx input⟩
theorem run_deterministic {P : Core.Problem} (C : Capability P) (ctx)
    (input : Input C ctx) (a b : ExecutionResult C ctx)
    (ha : a = run C ctx input) (hb : b = run C ctx input) : a = b :=
  ha.trans hb.symm
theorem outcome_exhaustive {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (r : ExecutionResult C ctx) :
    r.terminal = .tierOne ∨ r.terminal = .overlap ∨
      r.terminal = .deficit ∨ r.terminal = .reconciled := by
  cases r with
  | mk _ _ outcome =>
    cases outcome with
    | tierOne _ => exact Or.inl rfl
    | overlap _ => exact Or.inr (Or.inl rfl)
    | deficit _ => exact Or.inr (Or.inr (Or.inl rfl))
    | reconciled _ => exact Or.inr (Or.inr (Or.inr rfl))
end StructuralExhaustion.CT13
