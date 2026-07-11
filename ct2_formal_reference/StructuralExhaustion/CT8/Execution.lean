import StructuralExhaustion.CT8.Nodes
import StructuralExhaustion.CT8.Graph
namespace StructuralExhaustion.CT8

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  equivalence : Nodes.Equivalence.Plan F input
  repetition : Nodes.Repetition.Plan F input
  response : Nodes.Response.Plan F input
  routing : Nodes.Routing.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct10 (payload : CT10Payload F input) : RawOutcome F input .ct10
  | c5 {equality : EqualityState F input}
      (certificate : C5Certificate F input equality) : RawOutcome F input .c5
  | c2 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      (certificate : C2Certificate F input repeated) : RawOutcome F input .c2
  | ct3 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT3Payload F input separating) : RawOutcome F input .ct3
  | ct7 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT7Payload F input separating) : RawOutcome F input .ct7

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
  | .refine payload =>
      ⟨.ct10, .cons .beginScope (.cons (.scopeRefine payload) (.nil .ct10Terminal)),
        .ct10 payload⟩
  | .ready scopeState =>
      let equality := Nodes.Equivalence.run plan.equivalence scopeState
      match Nodes.Repetition.run plan.repetition equality with
      | .short certificate =>
          ⟨.c5,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.equivalenceCertified equality)
                  (.cons (.repetitionShort certificate) (.nil .c5Terminal)))),
            .c5 certificate⟩
      | .repeated repeated =>
          match Nodes.Response.run plan.response repeated with
          | .close certificate =>
              ⟨.c2,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equality)
                      (.cons (.repetitionRepeated repeated)
                        (.cons (.responseClose certificate) (.nil .c2Terminal))))),
                .c2 certificate⟩
          | .separating separating =>
              match Nodes.Routing.run plan.routing separating with
              | .toCT3 payload =>
                  ⟨.ct3,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.equivalenceCertified equality)
                          (.cons (.repetitionRepeated repeated)
                            (.cons (.responseSeparating separating)
                              (.cons (.routingToCT3 payload) (.nil .ct3Terminal)))))),
                    .ct3 payload⟩
              | .toCT7 payload =>
                  ⟨.ct7,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.equivalenceCertified equality)
                          (.cons (.repetitionRepeated repeated)
                            (.cons (.responseSeparating separating)
                              (.cons (.routingToCT7 payload) (.nil .ct7Terminal)))))),
                    .ct7 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct10 (payload : CT10Payload F input)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10
  | c5 {equality : EqualityState F input}
      (certificate : C5Certificate F input equality) : Outcome F input port .c5
  | c2 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      (certificate : C2Certificate F input repeated) : Outcome F input port .c2
  | ct3 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT3Payload F input separating)
      (accepted : port.accepts (.ct3 payload)) : Outcome F input port .ct3
  | ct7 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT7Payload F input separating)
      (accepted : port.accepts (.ct7 payload)) : Outcome F input port .ct7

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct10 payload _ => port.accepts (.ct10 payload)
  | .c5 _ => F.entry.C5Claim input.G input.branch
  | .c2 _ => F.entry.C2Claim input.G input.branch
  | .ct3 payload _ => port.accepts (.ct3 payload)
  | .ct7 payload _ => port.accepts (.ct7 payload)

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
  | ⟨_, path, .ct10 payload⟩ =>
      ⟨.ct10, path, .ct10 payload (handoff.accept (.ct10 payload))⟩
  | ⟨_, path, .c5 certificate⟩ => ⟨.c5, path, .c5 certificate⟩
  | ⟨_, path, .c2 certificate⟩ => ⟨.c2, path, .c2 certificate⟩
  | ⟨_, path, .ct3 payload⟩ =>
      ⟨.ct3, path, .ct3 payload (handoff.accept (.ct3 payload))⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩

def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    ExecutionResult F input port := certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩
end StructuralExhaustion.CT8
