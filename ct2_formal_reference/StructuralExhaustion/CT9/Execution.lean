import StructuralExhaustion.CT9.Nodes
import StructuralExhaustion.CT9.Graph
namespace StructuralExhaustion.CT9
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  fibre : Nodes.Fibre.Plan F input
  overload : Nodes.Overload.Plan F input
  extraction : Nodes.Extraction.Plan F input
  routing : Nodes.Routing.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct10 (payload : CT10Payload F input) : RawOutcome F input .ct10
  | ct4 {fibre : FibreState F input} (payload : CT4Payload F input fibre) :
      RawOutcome F input .ct4
  | c1 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (certificate : C1Certificate F input extraction) : RawOutcome F input .c1
  | ct7 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT7Payload F input extraction) : RawOutcome F input .ct7
  | ct8 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT8Payload F input extraction) : RawOutcome F input .ct8
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
      let fibre := Nodes.Fibre.run plan.fibre scopeState
      match Nodes.Overload.run plan.overload fibre with
      | .bounded payload =>
          ⟨.ct4,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.fibreCertified fibre)
                  (.cons (.overloadBounded payload) (.nil .ct4Terminal)))),
            .ct4 payload⟩
      | .overloaded overloaded =>
          let extraction := Nodes.Extraction.run plan.extraction overloaded
          match Nodes.Routing.run plan.routing extraction with
          | .close certificate =>
              ⟨.c1,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.fibreCertified fibre)
                      (.cons (.overloadPresent overloaded)
                        (.cons (.extractionCertified extraction)
                          (.cons (.routingClose certificate) (.nil .c1Terminal)))))),
                .c1 certificate⟩
          | .toCT7 payload =>
              ⟨.ct7,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.fibreCertified fibre)
                      (.cons (.overloadPresent overloaded)
                        (.cons (.extractionCertified extraction)
                          (.cons (.routingToCT7 payload) (.nil .ct7Terminal)))))),
                .ct7 payload⟩
          | .toCT8 payload =>
              ⟨.ct8,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.fibreCertified fibre)
                      (.cons (.overloadPresent overloaded)
                        (.cons (.extractionCertified extraction)
                          (.cons (.routingToCT8 payload) (.nil .ct8Terminal)))))),
                .ct8 payload⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct10 (payload : CT10Payload F input) (accepted : port.accepts (.ct10 payload)) :
      Outcome F input port .ct10
  | ct4 {fibre : FibreState F input} (payload : CT4Payload F input fibre)
      (accepted : port.accepts (.ct4 payload)) : Outcome F input port .ct4
  | c1 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (certificate : C1Certificate F input extraction) : Outcome F input port .c1
  | ct7 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT7Payload F input extraction) (accepted : port.accepts (.ct7 payload)) :
      Outcome F input port .ct7
  | ct8 {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT8Payload F input extraction) (accepted : port.accepts (.ct8 payload)) :
      Outcome F input port .ct8
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct10 payload _ => port.accepts (.ct10 payload)
  | .ct4 payload _ => port.accepts (.ct4 payload)
  | .c1 _ => F.entry.C1Claim input.G input.branch
  | .ct7 payload _ => port.accepts (.ct7 payload)
  | .ct8 payload _ => port.accepts (.ct8 payload)
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
  | ⟨_, path, .ct4 payload⟩ =>
      ⟨.ct4, path, .ct4 payload (handoff.accept (.ct4 payload))⟩
  | ⟨_, path, .c1 certificate⟩ => ⟨.c1, path, .c1 certificate⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩
  | ⟨_, path, .ct8 payload⟩ =>
      ⟨.ct8, path, .ct8 payload (handoff.accept (.ct8 payload))⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩
end StructuralExhaustion.CT9
