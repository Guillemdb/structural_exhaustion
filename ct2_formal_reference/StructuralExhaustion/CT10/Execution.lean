import StructuralExhaustion.CT10.Nodes
import StructuralExhaustion.CT10.Graph
namespace StructuralExhaustion.CT10
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  labels : Nodes.Labels.Plan F input
  classification : Nodes.Classification.Plan F input
  direct : Nodes.Direct.Plan F input
  promotion : Nodes.Promotion.Plan F input
  promotedRouting : Nodes.PromotedRouting.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | c5 {labels : LabelState F input} (certificate : C5Certificate F input labels) :
      RawOutcome F input .c5
  | ct3 (payload : CT3Payload F input) : RawOutcome F input .ct3
  | ct7 {labels : LabelState F input} {direct : DirectState F input labels}
      (payload : CT7Payload F input direct) : RawOutcome F input .ct7
  | ct15 {labels : LabelState F input} {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : CT15Payload F input promoted) : RawOutcome F input .ct15
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
  | .ready scopeState =>
      let labels := Nodes.Labels.run plan.labels scopeState
      match Nodes.Classification.run plan.classification labels with
      | .close certificate =>
          ⟨.c5,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.labelsCertified labels)
                  (.cons (.classificationClose certificate) (.nil .c5Terminal)))),
            .c5 certificate⟩
      | .direct direct =>
          match Nodes.Direct.run plan.direct direct with
          | .toCT3 payload =>
              ⟨.ct3,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.labelsCertified labels)
                      (.cons (.classificationDirect direct)
                        (.cons (.directToCT3 payload) (.nil .ct3Terminal))))),
                .ct3 (.direct payload)⟩
          | .toCT7 payload =>
              ⟨.ct7,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.labelsCertified labels)
                      (.cons (.classificationDirect direct)
                        (.cons (.directToCT7 payload) (.nil .ct7Terminal))))),
                .ct7 payload⟩
      | .missing missing =>
          let promoted := Nodes.Promotion.run plan.promotion missing
          match Nodes.PromotedRouting.run plan.promotedRouting promoted with
          | .toCT3 payload =>
              ⟨.ct3,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.labelsCertified labels)
                      (.cons (.classificationMissing missing)
                        (.cons (.promotionCertified promoted)
                          (.cons (.promotedToCT3 payload) (.nil .ct3Terminal)))))),
                .ct3 (.promoted payload)⟩
          | .toCT15 payload =>
              ⟨.ct15,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.labelsCertified labels)
                      (.cons (.classificationMissing missing)
                        (.cons (.promotionCertified promoted)
                          (.cons (.promotedToCT15 payload) (.nil .ct15Terminal)))))),
                .ct15 payload⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | c5 {labels : LabelState F input} (certificate : C5Certificate F input labels) :
      Outcome F input port .c5
  | ct3 (payload : CT3Payload F input) (accepted : port.accepts (.ct3 payload)) :
      Outcome F input port .ct3
  | ct7 {labels : LabelState F input} {direct : DirectState F input labels}
      (payload : CT7Payload F input direct) (accepted : port.accepts (.ct7 payload)) :
      Outcome F input port .ct7
  | ct15 {labels : LabelState F input} {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : CT15Payload F input promoted) (accepted : port.accepts (.ct15 payload)) :
      Outcome F input port .ct15
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .c5 _ => F.entry.C5Claim input.G input.branch
  | .ct3 payload _ => port.accepts (.ct3 payload)
  | .ct7 payload _ => port.accepts (.ct7 payload)
  | .ct15 payload _ => port.accepts (.ct15 payload)
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
  | ⟨_, path, .c5 certificate⟩ => ⟨.c5, path, .c5 certificate⟩
  | ⟨_, path, .ct3 payload⟩ =>
      ⟨.ct3, path, .ct3 payload (handoff.accept (.ct3 payload))⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩
  | ⟨_, path, .ct15 payload⟩ =>
      ⟨.ct15, path, .ct15 payload (handoff.accept (.ct15 payload))⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩
end StructuralExhaustion.CT10
