import Hypostructure.CT17.Execution

/-!
# CT17 soundness, totality, and exact-work theorems
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}

/-- Compatibility over precisely the target and offset schedules inherited by
the invocation. -/
def ScheduledCompatibility (capability : Capability spec)
    (previous : Previous) : Prop :=
  forall target,
    target ∈ (capability.targetsAt previous).values ->
      forall offset,
        offset ∈ (capability.offsetsAt previous).values ->
          spec.Compatible previous target offset

namespace CompatibleState

/-- The Core exhaustive miss is exactly scheduled compatibility. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    (state : CompatibleState capability previous) :
    ScheduledCompatibility capability previous := by
  intro target targetMember offset offsetMember
  exact state.compatible target targetMember offset offsetMember

end CompatibleState

namespace IncompatibilityResidual

/-- Every pair before the first incompatible pair is compatible. -/
theorem prefix_compatible {capability : Capability spec}
    {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    forall pair,
      pair ∈ (capability.pairScheduleAt previous).values.take
        residual.index.1 ->
      spec.Compatible previous pair.1 pair.2 := by
  intro pair member
  by_contra incompatible
  exact residual.first pair member (by
    simpa [Incompatible] using incompatible)

end IncompatibilityResidual

/-- Complete semantic claim advertised by each CT17 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .incompatibility, .incompatibility residual =>
      capability.scaleAt previous ∈ (capability.scalesAt previous).values ∧
      residual.target ∈ (capability.targetsAt previous).values ∧
      residual.offset ∈ (capability.offsetsAt previous).values ∧
      Not (spec.Compatible previous residual.target residual.offset) ∧
      (forall pair,
        pair ∈ (capability.pairScheduleAt previous).values.take
          residual.index.1 ->
        spec.Compatible previous pair.1 pair.2)
  | .exhausted, .exhausted _compatible _finite certificate =>
      capability.scaleAt previous ∈ (capability.scalesAt previous).values ∧
      ScheduledCompatibility capability previous ∧
      capability.scaleAt previous <= capability.scaleLimitAt previous ∧
      certificate.enumeration.survivors =
        survivorList capability previous ∧
      certificate.enumeration.survivors.Nodup ∧
      (forall position,
        position ∈ (capability.positionsAt previous).values ->
          Not (Survives capability previous position))
  | .survivors, .survivors _compatible _finite residual =>
      capability.scaleAt previous ∈ (capability.scalesAt previous).values ∧
      ScheduledCompatibility capability previous ∧
      capability.scaleAt previous <= capability.scaleLimitAt previous ∧
      residual.enumeration.survivors =
        survivorList capability previous ∧
      residual.enumeration.survivors = residual.first :: residual.remaining ∧
      residual.first ∈ (capability.positionsAt previous).values ∧
      Survives capability previous residual.first ∧
      (forall position,
        position ∈ (capability.positionsAt previous).values ->
          (position ∈ residual.enumeration.survivors <->
            Survives capability previous position))
  | .targetHit, .targetHit _compatible _orbitScale certificate =>
      capability.scaleAt previous ∈ (capability.scalesAt previous).values ∧
      ScheduledCompatibility capability previous ∧
      capability.scaleLimitAt previous < capability.scaleAt previous ∧
      certificate.value ∈ (capability.pairScheduleAt previous).values ∧
      spec.orbitValue previous (capability.scaleAt previous)
          certificate.offset =
        spec.targetValue previous certificate.target
  | .orbit, .orbit _compatible _orbitScale residual =>
      capability.scaleAt previous ∈ (capability.scalesAt previous).values ∧
      ScheduledCompatibility capability previous ∧
      capability.scaleLimitAt previous < capability.scaleAt previous ∧
      residual.values = (capability.offsetsAt previous).values.map
        (spec.orbitValue previous (capability.scaleAt previous)) ∧
      OrbitAvoids capability previous

namespace Outcome

/-- Every framework-generated outcome proves its exact branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | incompatibility residual =>
      exact ⟨capability.scaleAt_mem previous, residual.target_mem,
        residual.offset_mem, residual.incompatible,
        residual.prefix_compatible⟩
  | exhausted compatible finite certificate =>
      exact ⟨capability.scaleAt_mem previous, compatible.scheduled,
        finite.finite, certificate.enumeration.exact,
        certificate.enumeration.nodup, certificate.exhausted⟩
  | survivors compatible finite residual =>
      refine ⟨capability.scaleAt_mem previous, compatible.scheduled,
        finite.finite, residual.enumeration.exact, residual.exact,
        residual.first_mem, residual.first_survives, ?_⟩
      intro position scheduled
      constructor
      · exact residual.enumeration.sound position
      · exact residual.enumeration.complete position scheduled
  | targetHit compatible orbitScale certificate =>
      exact ⟨capability.scaleAt_mem previous, compatible.scheduled,
        orbitScale.large, certificate.member, certificate.equal⟩
  | orbit compatible orbitScale residual =>
      exact ⟨capability.scaleAt_mem previous, compatible.scheduled,
        orbitScale.large, residual.values_exact, residual.avoids⟩

/-- No terminal outside the five CT17 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .incompatibility ∨ terminal = .exhausted ∨
      terminal = .survivors ∨ terminal = .targetHit ∨ terminal = .orbit := by
  cases outcome with
  | incompatibility _ => exact Or.inl rfl
  | exhausted _ _ _ => exact Or.inr (Or.inl rfl)
  | survivors _ _ _ => exact Or.inr (Or.inr (Or.inl rfl))
  | targetHit _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | orbit _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete observable trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT17 is total, exactly traced, polynomially bounded, and retains the
literal predecessor. -/
theorem run_total
    (spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .incompatibility ∨ result.terminal = .exhausted ∨
      result.terminal = .survivors ∨ result.terminal = .targetHit ∨
        result.terminal = .orbit :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT17
