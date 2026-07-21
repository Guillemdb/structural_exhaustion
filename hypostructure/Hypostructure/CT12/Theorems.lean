import Hypostructure.CT12.Execution

/-!
# CT12 soundness, termination, and work theorems
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous}

/-- Exact check count determined by the terminal and iteration count. -/
def exactChecks : Terminal -> Nat -> Nat
  | .exhausted, iterations => 4 * iterations + 1
  | .demand, iterations => 4 * iterations
  | .tier, iterations => 4 * iterations

/-- Exact number of loop-trace nodes determined by the terminal and iteration
count.  The public trace has one additional entry node. -/
def exactLoopNodeCount : Terminal -> Nat -> Nat
  | .exhausted, iterations => 4 * iterations + 2
  | .demand, iterations => 4 * iterations
  | .tier, iterations => 4 * iterations

/-- A terminal is sound precisely when it arose from an exact generated
peeling step, or from an actual load-zero state. -/
def OutcomeClaim {previous : Previous} :
    {terminal : Terminal} -> Outcome spec previous terminal -> Prop
  | .exhausted, .exhausted _certificate =>
      Nonempty (spec.State previous 0)
  | .demand, .demand residual =>
      Exists fun load : Nat => Exists fun state : spec.State previous (load + 1) =>
        Exists fun step : PeelStep spec previous state =>
          step.selected = .demand residual
  | .tier, .tier residual =>
      Exists fun load : Nat => Exists fun state : spec.State previous (load + 1) =>
        Exists fun step : PeelStep spec previous state =>
          step.selected = .tier residual

/-- Every step in a trace uses the restoration selected from the exact options
computed for that peeled predecessor state.  Strict continuation decrease is
already a field of the typed `LoopTrace.continue` constructor. -/
def TraceClaim {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) : Prop :=
  match trace with
  | .exhausted _ => True
  | .demand _ step _residual _selected =>
      List.Mem step.selected (spec.restorations step.peeled).toList
  | .tier _ step _residual _selected =>
      List.Mem step.selected (spec.restorations step.peeled).toList
  | .continue _ step _nextState _decreases _selected tail =>
      List.Mem step.selected (spec.restorations step.peeled).toList ∧
        TraceClaim tail

namespace LoopTrace

/-- Every trace-derived terminal satisfies its exact semantic claim. -/
theorem outcome_verified {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    OutcomeClaim trace.outcome := by
  induction trace with
  | exhausted state => exact ⟨state⟩
  | demand state step residual selected =>
      exact ⟨_, state, step, selected⟩
  | tier state step residual selected =>
      exact ⟨_, state, step, selected⟩
  | «continue» _state _step _nextState _decreases _selected _tail induction =>
      exact induction

/-- Every generated trace uses only exact predecessor-derived restoration
options at every iteration. -/
theorem trace_verified {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    TraceClaim trace := by
  induction trace with
  | exhausted => trivial
  | demand _state step _residual _selected =>
      exact step.selected_from_exact_options
  | tier _state step _residual _selected =>
      exact step.selected_from_exact_options
  | «continue» _state step _nextState _decreases _selected _tail induction =>
      exact ⟨step.selected_from_exact_options, induction⟩

/-- The number of positive peeling steps cannot exceed the initial load. -/
theorem iterations_le_load {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    trace.iterations <= load := by
  induction trace with
  | exhausted => simp [iterations]
  | demand => simp [iterations]
  | tier => simp [iterations]
  | «continue» _state _step _nextState decreases _selected _tail induction =>
      simp only [iterations]
      omega

/-- Exact branch-sensitive primitive work. -/
theorem checks_eq_exact {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    trace.checks = exactChecks terminal trace.iterations := by
  induction trace with
  | exhausted => rfl
  | demand => rfl
  | tier => rfl
  | @«continue» _current _next _state _step _nextState _decreases _selected
      terminal tail induction =>
      cases terminal <;>
        simp [checks, iterations, exactChecks, induction] <;> omega

/-- Exact loop-node count of every typed trace. -/
theorem nodes_length_eq_exact {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    trace.nodes.length = exactLoopNodeCount terminal trace.iterations := by
  induction trace with
  | exhausted => rfl
  | demand => rfl
  | tier => rfl
  | @«continue» _current _next _state _step _nextState _decreases _selected
      terminal tail induction =>
      cases terminal <;>
        simp [nodes, iterations, exactLoopNodeCount, induction] <;> omega

/-- Exact work is bounded by the framework load envelope. -/
theorem checks_le_maximum {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    trace.checks <= maximumChecks load := by
  rw [trace.checks_eq_exact]
  have bounded := trace.iterations_le_load
  cases terminal <;> simp [exactChecks, maximumChecks] <;> omega

end LoopTrace

/-- The recursion is total at every indexed state.  Lean accepts `runLoop`
only because the continuation branch consumes its stored strict decrease. -/
theorem runLoop_terminates
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) (load : Nat)
    (state : spec.State previous load) :
    Exists fun terminal : Terminal =>
      Nonempty (LoopTrace spec previous load state terminal) :=
  ⟨(runLoop spec previous load state).terminal,
    ⟨(runLoop spec previous load state).trace⟩⟩

/-- The load order used by CT12 is well-founded independently of any domain. -/
theorem loadOrder_wellFounded :
    WellFounded (fun next current : Nat => next < current) :=
  Nat.lt_wfRel.wf

namespace Outcome

/-- No terminal outside the three CT12 alternatives is constructible. -/
theorem terminal_exhaustive {previous : Previous} {terminal : Terminal}
    (outcome : Outcome spec previous terminal) :
    terminal = .exhausted ∨ terminal = .demand ∨ terminal = .tier := by
  cases outcome with
  | exhausted _ => exact Or.inl rfl
  | demand _ => exact Or.inr (Or.inl rfl)
  | tier _ => exact Or.inr (Or.inr rfl)

end Outcome

namespace ExecutionResult

/-- Every generated execution is semantically sound. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.stage.added.trace.outcome_verified

/-- Every intermediate restoration in the generated trace came from the exact
predecessor-derived options. -/
theorem trace_verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    TraceClaim result.stage.added.trace :=
  result.stage.added.trace.trace_verified

/-- Exact iteration bound inherited from the indexed trace. -/
theorem iterations_le_initialLoad {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.iterations <=
      (capability.initialAt result.stage.previous).load :=
  result.stage.added.trace.iterations_le_load

/-- Exact branch-sensitive work equation. -/
theorem checks_eq_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = exactChecks result.terminal result.iterations :=
  result.stage.added.trace.checks_eq_exact

/-- Exact public trace length, including the entry node. -/
theorem trace_length_eq_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes.length =
      exactLoopNodeCount result.terminal result.iterations + 1 := by
  change (NodeId.entry :: result.stage.added.trace.nodes).length =
    exactLoopNodeCount result.stage.added.terminal
      result.stage.added.trace.iterations + 1
  simp only [List.length_cons]
  rw [result.stage.added.trace.nodes_length_eq_exact]

/-- Exact work fits the framework's initial-load envelope. -/
theorem checks_le_maximum {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      maximumChecks (capability.initialAt result.stage.previous).load :=
  result.stage.added.trace.checks_le_maximum

/-- Every execution satisfies the capability's polynomial work envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_maximum.trans
    (capability.workBound result.stage.previous)

end ExecutionResult

/-- Public execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT12 is total, terminating, exactly traced, polynomially bounded, and
retains its literal predecessor. -/
theorem run_total
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      TraceClaim result.stage.added.trace ∧
      result.iterations <= (capability.initialAt previous).load ∧
      result.checks = exactChecks result.terminal result.iterations ∧
      result.traceNodes.length =
        exactLoopNodeCount result.terminal result.iterations + 1 ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_verified,
    result.iterations_le_initialLoad,
    result.checks_eq_exact, result.trace_length_eq_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for one completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .exhausted ∨ result.terminal = .demand ∨
      result.terminal = .tier :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT12
