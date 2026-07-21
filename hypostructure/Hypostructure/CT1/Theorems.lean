import Hypostructure.CT1.Execution

/-!
# CT1 soundness and totality
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Semantic proposition advertised by a CT1 terminal. -/
def OutcomeClaim {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) : Terminal -> Prop
  | .c1 => Target spec previous (capability.scheduleAt previous)
  | .avoiding => Not (Target spec previous (capability.scheduleAt previous))

/-- A Core-routed scan proves exactly the claim of its derived terminal. -/
theorem routed_verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (routed : RoutedSearch spec capability previous) :
    OutcomeClaim spec capability previous (terminalOfRoute routed) := by
  cases branch : routed.added with
  | yesBranch hasHit =>
      simpa [OutcomeClaim, terminalOfRoute, branch] using
        C1Certificate.target (routed.previous.hitOfHasHit hasHit)
  | noBranch avoids =>
      simpa [OutcomeClaim, terminalOfRoute, branch] using
        AvoidingState.targetAvoiding avoids

namespace ExecutionResult

/-- Aggregate semantic soundness of a completed CT1 execution. -/
theorem verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim spec capability result.stage.previous result.terminal :=
  routed_verified result.stage.added

/-- Every typed trace is the exact reference trace for its terminal. -/
theorem trace_exact {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes =
      Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- A realized scheduled target forces the routed result to the C1 terminal. -/
theorem terminal_c1_of_target {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (target : Target spec result.stage.previous
      (capability.scheduleAt result.stage.previous)) :
    result.terminal = .c1 := by
  cases branch : result.stage.added.added with
  | yesBranch _ =>
      simp [ExecutionResult.terminal, terminalOfRoute, branch]
  | noBranch avoids =>
      exact (AvoidingState.targetAvoiding avoids target).elim

/-- Reaching C1 means that at least one primitive candidate was inspected. -/
theorem checks_pos_of_c1 {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (terminal : result.terminal = .c1) : 0 < result.checks := by
  cases branch : result.stage.added.added with
  | noBranch _ =>
      simp [ExecutionResult.terminal, terminalOfRoute, branch] at terminal
  | yesBranch hasHit =>
      rw [result.checks_eq]
      cases found : result.stage.added.previous.hit? with
      | none =>
          simp [Core.Finite.Search.Execution.HasHit, found] at hasHit
      | some hit =>
          simp [Core.Finite.Accounting.executionChecks, found]

end ExecutionResult

/-- The public runner is semantically sound. -/
theorem run_verified {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim spec capability previous (run spec capability previous).terminal :=
  (run spec capability previous).verified

/-- CT1 is total, sound, traced, and work-bounded from its capability alone. -/
theorem run_total {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim spec capability previous result.terminal ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  refine ⟨result, rfl, result.verified, result.trace_exact, ?_⟩
  exact result.checks_le_polynomial

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the two CT1 outcomes is reachable. -/
theorem outcome_exhaustive {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .c1 ∨ result.terminal = .avoiding := by
  cases branch : result.stage.added.added <;>
    simp [ExecutionResult.terminal, terminalOfRoute, branch]

namespace TargetBridge

/-- Interpret an independently named target through an exact schedule bridge. -/
theorem target_of_publicTarget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    {PublicTarget : Previous -> Prop}
    (bridge : TargetBridge spec capability PublicTarget) {previous : Previous}
    (target : PublicTarget previous) :
    Target spec previous (capability.scheduleAt previous) :=
  (bridge.equivalent previous).mp target

/-- Decode one validated scheduled target to its public mathematical target. -/
theorem publicTarget_of_target {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    {PublicTarget : Previous -> Prop}
    (bridge : TargetBridge spec capability PublicTarget) {previous : Previous}
    (target : Target spec previous (capability.scheduleAt previous)) :
    PublicTarget previous :=
  (bridge.equivalent previous).mpr target

/-- Exact CT1 avoidance excludes the bridged public target. -/
theorem not_publicTarget_of_avoiding {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec}
    {PublicTarget : Previous -> Prop}
    (bridge : TargetBridge spec capability PublicTarget) {previous : Previous}
    (avoids : Not (Target spec previous (capability.scheduleAt previous))) :
    Not (PublicTarget previous) :=
  fun target => avoids (bridge.target_of_publicTarget target)

end TargetBridge

end Hypostructure.CT1
