import StructuralExhaustion.CT16.Execution

namespace StructuralExhaustion.CT16

def RawOutcome.Valid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {t} : RawOutcome C ctx t → Prop
  | .proper r => ¬ C.InSupport ctx.G r.missing
  | .equal c => C.closedCode ctx.G = C.targetCode
  | .mismatch r => C.closedCode ctx.G ≠ C.targetCode

theorem RawOutcome.verified {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {t} (o : RawOutcome C ctx t) : o.Valid := by
  cases o with
  | proper residual => exact residual.absent
  | equal certificate => exact certificate.state.exact.symm.trans certificate.equal
  | mismatch residual =>
      intro equal
      exact residual.notEqual (residual.state.exact.trans equal)

theorem ExecutionResult.traceValid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (r : ExecutionResult C ctx) :
    @Graph.ValidTrace P C ctx r.trace := ⟨r.terminal, r.path, rfl⟩
theorem run_verified {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    (run C ctx input).outcome.Valid := (run C ctx input).outcome.verified
theorem run_trace_valid {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    @Graph.ValidTrace P C ctx (run C ctx input).trace :=
  (run C ctx input).traceValid
theorem run_total {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    ∃ r : ExecutionResult C ctx, r.outcome.Valid ∧
      @Graph.ValidTrace P C ctx r.trace :=
  ⟨run C ctx input, run_verified C ctx input, run_trace_valid C ctx input⟩
theorem run_deterministic {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx)
    (a b : ExecutionResult C ctx) (ha : a = run C ctx input)
    (hb : b = run C ctx input) : a = b := ha.trans hb.symm
theorem outcome_exhaustive {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (r : ExecutionResult C ctx) :
    r.terminal = .proper ∨ r.terminal = .equal ∨ r.terminal = .mismatch := by
  cases r with
  | mk _ _ outcome =>
    cases outcome with
    | proper _ => exact Or.inl rfl
    | equal _ => exact Or.inr (Or.inl rfl)
    | mismatch _ => exact Or.inr (Or.inr rfl)

end StructuralExhaustion.CT16
