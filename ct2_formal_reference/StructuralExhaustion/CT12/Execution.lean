import StructuralExhaustion.CT12.Nodes
import StructuralExhaustion.CT12.Graph

namespace StructuralExhaustion.CT12

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  measure : Nodes.Measure.Plan F input
  saturation : Nodes.Saturation.Plan F input
  peel : Nodes.Peel.Plan F input
  restoration : Nodes.Restoration.Plan F input
  decrease : Nodes.Decrease.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | c4 {load : Nat} {state : LoopState F input load}
      (certificate : C4Certificate F input state) : RawOutcome F input .c4
  | ct4 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT4Payload F input peeled) : RawOutcome F input .ct4
  | ct13 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT13Payload F input peeled) : RawOutcome F input .ct13

structure LoopResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .saturationDecision terminal.nodeId
  outcome : RawOutcome F input terminal

/-- Exact recursive executor for CT12.  The recursive call is accepted only
through `DecreasedState.decreases`; restoration alone cannot license it. -/
def runLoop (F : Framework) (input : Input F) (plan : CorePlan F input)
    {load : Nat} (state : LoopState F input load) : LoopResult F input :=
  match Nodes.Saturation.run plan.saturation state with
  | .close certificate =>
      ⟨.c4, .cons (.saturationClose certificate) (.nil .c4Terminal), .c4 certificate⟩
  | .peel peelable =>
      let peeled := Nodes.Peel.run plan.peel peelable
      match Nodes.Restoration.run plan.restoration peeled with
      | .toCT4 payload =>
          ⟨.ct4,
            .cons (.saturationPeel peelable)
              (.cons (.peelCertified peeled)
                (.cons (.restorationToCT4 payload) (.nil .ct4Terminal))),
            .ct4 payload⟩
      | .toCT13 payload =>
          ⟨.ct13,
            .cons (.saturationPeel peelable)
              (.cons (.peelCertified peeled)
                (.cons (.restorationToCT13 payload) (.nil .ct13Terminal))),
            .ct13 payload⟩
      | .continue restored =>
          let decreased := Nodes.Decrease.run plan.decrease restored
          let tail := runLoop F input plan (DecreasedState.loopState decreased)
          ⟨tail.terminal,
            .cons (.saturationPeel peelable)
              (.cons (.peelCertified peeled)
                (.cons (.restorationContinue restored)
                  (.cons (.decreaseLoop decreased) tail.path))),
            tail.outcome⟩
termination_by load
decreasing_by exact decreased.decreases

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scope =>
      let state := Nodes.Measure.run plan.measure scope
      let loop := runLoop F input plan state
      ⟨loop.terminal,
        .cons .beginScope (.cons (.scopeReady scope)
          (.cons (.measureCertified state) loop.path)),
        loop.outcome⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | c4 {load : Nat} {state : LoopState F input load}
      (certificate : C4Certificate F input state) : Outcome F input port .c4
  | ct4 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT4Payload F input peeled) (accepted : port.accepts (.ct4 payload)) :
      Outcome F input port .ct4
  | ct13 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT13Payload F input peeled) (accepted : port.accepts (.ct13 payload)) :
      Outcome F input port .ct13

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .c4 _ => F.entry.C4Claim input.G input.branch
  | .ct4 p _ => port.accepts (.ct4 p)
  | .ct13 p _ => port.accepts (.ct13 p)

structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) : List Graph.NodeId := r.path.trace
end ExecutionResult

def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (r : CoreResult F input) : ExecutionResult F input port :=
  match r with
  | ⟨_, path, .scope c⟩ => ⟨.scope, path, .scope c⟩
  | ⟨_, path, .c4 c⟩ => ⟨.c4, path, .c4 c⟩
  | ⟨_, path, .ct4 p⟩ => ⟨.ct4, path, .ct4 p (handoff.accept (.ct4 p))⟩
  | ⟨_, path, .ct13 p⟩ => ⟨.ct13, path, .ct13 p (handoff.accept (.ct13 p))⟩

def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let r := runTraced F input plan port handoff
  ⟨r.terminal, r.outcome⟩

end StructuralExhaustion.CT12
