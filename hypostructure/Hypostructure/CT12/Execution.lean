import Hypostructure.CT12.Search

/-!
# CT12 well-founded accumulated execution

The recursive runner can continue only through a restoration that contains a
proof of strict load decrease.  Its typed trace retains every generated peel,
framework-selected restoration, and decrease.  Public execution performs one
extension of the literal predecessor ledger.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous}

/-- Typed loop trace.  Continuation edges retain both the selected restoration
equation and the strict decrease used by well-founded recursion. -/
inductive LoopTrace
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) :
    (load : Nat) -> spec.State previous load -> Terminal -> Type _ where
  | exhausted (state : spec.State previous 0) :
      LoopTrace spec previous 0 state .exhausted
  | demand {load : Nat} (state : spec.State previous (load + 1))
      (step : PeelStep spec previous state)
      (residual : spec.DemandResidual previous)
      (selected : step.selected = .demand residual) :
      LoopTrace spec previous (load + 1) state .demand
  | tier {load : Nat} (state : spec.State previous (load + 1))
      (step : PeelStep spec previous state)
      (residual : spec.TierResidual previous)
      (selected : step.selected = .tier residual) :
      LoopTrace spec previous (load + 1) state .tier
  | continue {load next : Nat}
      (state : spec.State previous (load + 1))
      (step : PeelStep spec previous state)
      (nextState : spec.State previous next)
      (decreases : next < load + 1)
      (selected : step.selected = .continue next nextState decreases)
      {terminal : Terminal}
      (tail : LoopTrace spec previous next nextState terminal) :
      LoopTrace spec previous (load + 1) state terminal

namespace LoopTrace

/-- Exact audit-node sequence below the CT12 entry node. -/
def nodes {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) : List NodeId :=
  match trace with
  | .exhausted _ => [.saturation, .exhaustedTerminal]
  | .demand _ _ _ _ =>
      [.saturation, .peel, .restoration, .demandTerminal]
  | .tier _ _ _ _ =>
      [.saturation, .peel, .restoration, .tierTerminal]
  | .continue _ _ _ _ _ tail =>
      [.saturation, .peel, .restoration, .decrease] ++ tail.nodes

/-- Number of positive-load states peeled by this exact trace. -/
def iterations {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) : Nat :=
  match trace with
  | .exhausted _ => 0
  | .demand _ _ _ _ => 1
  | .tier _ _ _ _ => 1
  | .continue _ _ _ _ _ tail => tail.iterations + 1

/-- Exact primitive checks charged by the framework accounting policy. -/
def checks {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) : Nat :=
  match trace with
  | .exhausted _ => 1
  | .demand _ _ _ _ => 4
  | .tier _ _ _ _ => 4
  | .continue _ _ _ _ _ tail => tail.checks + 4

/-- Terminal output is computed from the trace; callers never supply it. -/
def outcome {previous : Previous} {load : Nat}
    {state : spec.State previous load} {terminal : Terminal}
    (trace : LoopTrace spec previous load state terminal) :
    Outcome spec previous terminal :=
  match trace with
  | .exhausted state =>
      .exhausted (ExhaustedCertificate.ofState state)
  | .demand _ _ residual _ => .demand residual
  | .tier _ _ residual _ => .tier residual
  | .continue _ _ _ _ _ tail => tail.outcome

end LoopTrace

/-- Result of the terminating runner from one indexed state. -/
structure LoopResult
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) (load : Nat)
    (state : spec.State previous load) where
  terminal : Terminal
  trace : LoopTrace spec previous load state terminal

namespace LoopResult

/-- Semantic output derived from the generated typed trace. -/
def outcome {previous : Previous} {load : Nat}
    {state : spec.State previous load}
    (result : LoopResult spec previous load state) :
    Outcome spec previous result.terminal :=
  result.trace.outcome

end LoopResult

/-- Genuine well-founded structural peeling.  The only recursive call consumes
the strict inequality carried by `Restoration.continue`. -/
def runLoop
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) :
    (load : Nat) -> (state : spec.State previous load) ->
      LoopResult spec previous load state
  | 0, state =>
      { terminal := .exhausted, trace := .exhausted state }
  | load + 1, state =>
      let step := inspect spec previous state
      match selectedEquation : step.selected with
      | .demand residual =>
          { terminal := .demand
            trace := .demand state step residual selectedEquation }
      | .tier residual =>
          { terminal := .tier
            trace := .tier state step residual selectedEquation }
      | .continue next nextState decreases =>
          let recursive := runLoop spec previous next nextState
          { terminal := recursive.terminal
            trace := .continue state step nextState decreases
              selectedEquation recursive.trace }
termination_by load => load

/-- Private generated value installed in the accumulated ledger. -/
structure Routed
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  trace : LoopTrace spec previous (capability.initialAt previous).load
    (capability.initialAt previous).state terminal

namespace Routed

/-- Exact terminal output generated by the runner. -/
def outcome {capability : Capability spec} {previous : Previous}
    (routed : Routed spec capability previous) :
    Outcome spec previous routed.terminal :=
  routed.trace.outcome

/-- Complete observable trace, including the single entry node. -/
def traceNodes {capability : Capability spec} {previous : Previous}
    (routed : Routed spec capability previous) : List NodeId :=
  .entry :: routed.trace.nodes

/-- Exact number of positive-load peeling iterations. -/
def iterations {capability : Capability spec} {previous : Previous}
    (routed : Routed spec capability previous) : Nat :=
  routed.trace.iterations

/-- Exact primitive-check count. -/
def checks {capability : Capability spec} {previous : Previous}
    (routed : Routed spec capability previous) : Nat :=
  routed.trace.checks

end Routed

/-- Run CT12's canonical well-founded reference machine. -/
def routeReference
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    Routed spec capability previous :=
  let initial := capability.initialAt previous
  let loop := runLoop spec previous initial.load initial.state
  .mk loop.terminal loop.trace

/-- One CT12 execution is one extension of the literal incoming ledger. -/
abbrev Stage
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed spec capability previous

/-- Closed public result of one CT12 execution. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability

namespace ExecutionResult

/-- Framework-selected terminal. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Exact terminal-indexed output. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome spec result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Exact observable node trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.stage.added.traceNodes

/-- Exact number of positive-load peeling iterations. -/
def iterations {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.iterations

/-- Exact primitive-check count. -/
def checks {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.checks

end ExecutionResult

/-- Execute CT12 on one literal predecessor ledger. -/
def run
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  { stage := Core.Residual.Ledger.extend previous
      (routeReference spec capability previous) }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT12
