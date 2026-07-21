import Hypostructure.CT16.Execution

/-!
# CT16 soundness, totality, and exact terminal semantics
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Mathematical claim advertised by each semantic terminal. -/
def OutcomeClaim {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) : Terminal -> Prop
  | .properSupport =>
      Nonempty (ProperSupportResidual capability previous)
  | .exactCode =>
      ExactClosedType spec previous (capability.coordinatesAt previous)
  | .mismatch =>
      WholeSupport spec previous (capability.coordinatesAt previous) ∧
        spec.closedCode previous ≠ spec.targetCode previous

namespace Outcome

/-- Every framework-generated typed outcome proves its advertised claim. -/
theorem verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    OutcomeClaim spec capability previous terminal := by
  cases outcome with
  | properSupport residual => exact ⟨residual⟩
  | exactCode certificate =>
      exact ⟨certificate.state.whole.covers,
        certificate.state.exact.symm.trans certificate.equal⟩
  | mismatch residual =>
      refine ⟨residual.state.whole.covers, ?_⟩
      intro equal
      exact residual.notEqual (residual.state.exact.trans equal)

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness of a completed CT16 execution. -/
theorem verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim spec capability result.stage.previous result.terminal :=
  result.outcome.verified

/-- Every generated trace is the canonical trace of its derived terminal. -/
theorem trace_exact {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.stage.added.trace.nodes_eq_expected

end ExecutionResult

/-- The public runner is semantically sound. -/
theorem run_verified {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim spec capability previous (run spec capability previous).terminal :=
  (run spec capability previous).verified

/-- CT16 is total, sound, exactly traced, and linearly work-bounded. -/
theorem run_total {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim spec capability previous result.terminal ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks ≤ (capability.linearWorkBudget).coefficient *
        ((capability.linearWorkBudget).size previous + 1) ^
          (capability.linearWorkBudget).degree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the three CT16 outcomes is representable. -/
theorem outcome_exhaustive {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .properSupport ∨ result.terminal = .exactCode ∨
      result.terminal = .mismatch := by
  cases result.terminal <;> simp

end Hypostructure.CT16
