import StructuralExhaustion.CT16.Nodes
import StructuralExhaustion.CT16.Graph
namespace StructuralExhaustion.CT16
structure CorePlan (F : Framework) (input : Input F) where
  support : Nodes.Support.Plan F input
  scope : Nodes.Scope.Plan F input
  closedType : Nodes.ClosedType.Plan F input
  equality : Nodes.Equality.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | ct3 {proper : ProperState F input} (payload : CT3Payload F input proper) :
      RawOutcome F input .ct3
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | c2 {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (certificate : C2Certificate F input closed) :
      RawOutcome F input .c2
  | ct10 {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (payload : CT10Payload F input closed) :
      RawOutcome F input .ct10
structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal
def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Support.run entry plan.support with
  | .proper payload =>
      ⟨.ct3, .cons .beginSupport (.cons (.supportProper payload) (.nil .ct3Terminal)),
        .ct3 payload⟩
  | .whole whole =>
      match Nodes.Scope.run plan.scope whole with
      | .exit candidate =>
          ⟨.scope, .cons .beginSupport (.cons (.supportWhole whole)
            (.cons (.scopeExit whole candidate) (.nil .scopeTerminal))), .scope candidate⟩
      | .ready scope =>
          let closed := Nodes.ClosedType.run plan.closedType scope
          match Nodes.Equality.run plan.equality closed with
          | .equal certificate =>
              ⟨.c2, .cons .beginSupport (.cons (.supportWhole whole)
                (.cons (.scopeReady scope) (.cons (.closedTypeCertified closed)
                  (.cons (.equalityClose certificate) (.nil .c2Terminal))))), .c2 certificate⟩
          | .distinct payload =>
              ⟨.ct10, .cons .beginSupport (.cons (.supportWhole whole)
                (.cons (.scopeReady scope) (.cons (.closedTypeCertified closed)
                  (.cons (.equalityDistinct payload) (.nil .ct10Terminal))))), .ct10 payload⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | ct3 {proper : ProperState F input} (payload : CT3Payload F input proper)
      (accepted : port.accepts (.ct3 payload)) : Outcome F input port .ct3
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | c2 {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (certificate : C2Certificate F input closed) :
      Outcome F input port .c2
  | ct10 {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (payload : CT10Payload F input closed)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .ct3 p _ => port.accepts (.ct3 p) | .scope _ => ¬ ScopeReadyAt F input
  | .c2 _ => F.entry.C2Claim input.G input.branch | .ct10 p _ => port.accepts (.ct10 p)
structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) : List Graph.NodeId := r.path.trace
end ExecutionResult
def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .ct3 p⟩ => ⟨.ct3, path, .ct3 p (handoff.accept (.ct3 p))⟩
  | ⟨_, path, .scope c⟩ => ⟨.scope, path, .scope c⟩
  | ⟨_, path, .c2 c⟩ => ⟨.c2, path, .c2 c⟩
  | ⟨_, path, .ct10 p⟩ => ⟨.ct10, path, .ct10 p (handoff.accept (.ct10 p))⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let r := runTraced F input plan port handoff; ⟨r.terminal, r.outcome⟩
end StructuralExhaustion.CT16
