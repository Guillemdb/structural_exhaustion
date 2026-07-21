import Hypostructure.CT7.Execution

/-!
# CT7 soundness, totality, and terminal semantics
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Mathematical claim advertised by each generated terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .realization, .realization certificate =>
      spec.Realizes previous (capability.representativesAt previous).source
        certificate.context
  | .distinguishing, .distinguishing residual =>
      (forall context, Not (spec.Realizes previous
        (capability.representativesAt previous).source context)) ∧
      spec.system.contextResponse
          (capability.representativesAt previous).source residual.context ≠
        spec.system.contextResponse
          (capability.representativesAt previous).replacement residual.context
  | .neutral, .neutral _certificate =>
      (forall context, Not (spec.Realizes previous
        (capability.representativesAt previous).source context)) ∧
      Core.Response.UniversalNeutrality spec.system
        (capability.representativesAt previous)

namespace Outcome

/-- Every framework-generated typed outcome proves its advertised claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | realization certificate => exact certificate.realizes
  | distinguishing residual =>
      exact ⟨residual.noRealization, residual.contextDiffers⟩
  | neutral certificate =>
      exact ⟨certificate.noRealization, certificate.universal⟩

/-- Any semantic realizing context forces the realization terminal. -/
theorem terminal_realization_of_exists
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (existsRealization : Exists fun context =>
      spec.Realizes previous (capability.representativesAt previous).source
        context) :
    terminal = .realization := by
  obtain ⟨context, realizes⟩ := existsRealization
  cases outcome with
  | realization _ => rfl
  | distinguishing residual =>
      exact (residual.noRealization context realizes).elim
  | neutral certificate =>
      exact (certificate.noRealization context realizes).elim

/-- Exhaustive absence of realization together with any semantic response
difference forces the distinguishing terminal. -/
theorem terminal_distinguishing_of_difference
    {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal)
    (noRealization : forall context, Not (spec.Realizes previous
      (capability.representativesAt previous).source context))
    (existsDifference : Exists fun context =>
      spec.system.contextResponse
          (capability.representativesAt previous).source context ≠
        spec.system.contextResponse
          (capability.representativesAt previous).replacement context) :
    terminal = .distinguishing := by
  obtain ⟨context, differs⟩ := existsDifference
  cases outcome with
  | realization certificate =>
      exact (noRealization certificate.context certificate.realizes).elim
  | distinguishing _ => rfl
  | neutral certificate =>
      exact (differs (certificate.universal.equalInContext context)).elim

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete reference trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- Semantic realization forces the generated result's realization terminal. -/
theorem terminal_realization_of_exists {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (existsRealization : Exists fun context =>
      spec.Realizes result.stage.previous
        (capability.representativesAt result.stage.previous).source context) :
    result.terminal = .realization :=
  result.outcome.terminal_realization_of_exists existsRealization

/-- Semantic non-realization plus response difference forces the generated
result's distinguishing terminal. -/
theorem terminal_distinguishing_of_difference
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (noRealization : forall context, Not (spec.Realizes result.stage.previous
      (capability.representativesAt result.stage.previous).source context))
    (existsDifference : Exists fun context =>
      spec.system.contextResponse
          (capability.representativesAt result.stage.previous).source context ≠
        spec.system.contextResponse
          (capability.representativesAt result.stage.previous).replacement
            context) :
    result.terminal = .distinguishing :=
  result.outcome.terminal_distinguishing_of_difference noRealization
    existsDifference

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT7 is total, sound, exactly traced, linearly bounded, and predecessor
preserving. -/
theorem run_total
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks ≤ (capability.linearWorkBudget).coefficient *
        ((capability.linearWorkBudget).size previous + 1) ^
          (capability.linearWorkBudget).degree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the three CT7 alternatives is representable. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .realization ∨
      result.terminal = .distinguishing ∨
      result.terminal = .neutral := by
  cases result.terminal <;> simp

/-- A neutral terminal transports any exact target semantics through every
semantic context. -/
theorem NeutralityCertificate.target_iff
    {capability : Capability spec} {previous : Previous}
    (certificate : NeutralityCertificate capability previous)
    (semantics : Core.Response.TargetSemantics spec.system)
    (context : spec.system.Context) :
    semantics.TargetResponse (capability.representativesAt previous).source
        context ↔
      semantics.TargetResponse
        (capability.representativesAt previous).replacement context :=
  (certificate.targetComplete semantics).targetIff context

end Hypostructure.CT7
