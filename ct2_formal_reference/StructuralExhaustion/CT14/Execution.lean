import StructuralExhaustion.CT14.Nodes
import StructuralExhaustion.CT14.Graph
namespace StructuralExhaustion.CT14
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  bounds : Nodes.Bounds.Plan F input
  multiplicity : Nodes.Multiplicity.Plan F input
  comparison : Nodes.Comparison.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct9 {bounds : BoundsState F input} (payload : CT9Payload F input bounds) :
      RawOutcome F input .ct9
  | ct10 {bounds : BoundsState F input} (payload : CT10Payload F input bounds) :
      RawOutcome F input .ct10
  | c4 {bounds : BoundsState F input} {multiplicity : MultiplicityState F input bounds}
      (certificate : C4Certificate F input multiplicity) : RawOutcome F input .c4
structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal
def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) :
    CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scope =>
      let bounds := Nodes.Bounds.run plan.bounds scope
      match Nodes.Multiplicity.run plan.multiplicity bounds with
      | .unbounded payload =>
          ⟨.ct9,
            .cons .beginScope (.cons (.scopeReady scope)
              (.cons (.boundsCertified bounds)
                (.cons (.multiplicityUnbounded payload) (.nil .ct9Terminal)))),
            .ct9 payload⟩
      | .missingLabel payload =>
          ⟨.ct10,
            .cons .beginScope (.cons (.scopeReady scope)
              (.cons (.boundsCertified bounds)
                (.cons (.multiplicityMissing payload) (.nil .ct10Terminal)))),
            .ct10 payload⟩
      | .counted multiplicity =>
          let certificate := Nodes.Comparison.run plan.comparison multiplicity
          ⟨.c4,
            .cons .beginScope (.cons (.scopeReady scope)
              (.cons (.boundsCertified bounds)
                (.cons (.multiplicityCounted multiplicity)
                  (.cons (.comparisonClose certificate) (.nil .c4Terminal))))),
            .c4 certificate⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct9 {bounds : BoundsState F input} (payload : CT9Payload F input bounds)
      (accepted : port.accepts (.ct9 payload)) : Outcome F input port .ct9
  | ct10 {bounds : BoundsState F input} (payload : CT10Payload F input bounds)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10
  | c4 {bounds : BoundsState F input} {multiplicity : MultiplicityState F input bounds}
      (certificate : C4Certificate F input multiplicity) : Outcome F input port .c4
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct9 payload _ => port.accepts (.ct9 payload)
  | .ct10 payload _ => port.accepts (.ct10 payload)
  | .c4 _ => F.entry.C4Claim input.G input.branch
structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId := result.path.trace
end ExecutionResult
def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (result : CoreResult F input) :
    ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ => ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .ct9 payload⟩ => ⟨.ct9, path, .ct9 payload (handoff.accept (.ct9 payload))⟩
  | ⟨_, path, .ct10 payload⟩ => ⟨.ct10, path, .ct10 payload (handoff.accept (.ct10 payload))⟩
  | ⟨_, path, .c4 certificate⟩ => ⟨.c4, path, .c4 certificate⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩
end StructuralExhaustion.CT14
