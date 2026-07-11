import StructuralExhaustion.CT6.Nodes
import StructuralExhaustion.CT6.Graph

namespace StructuralExhaustion.CT6

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  definition : Nodes.Definition.Plan F input
  activity : Nodes.Activity.Plan F input
  activeLedger : Nodes.ActiveLedger.Plan F input
  dormant : Nodes.Dormant.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct4 {definition : DefinitionState F input}
      {active : ActiveState F input definition}
      (payload : CT4Payload F input active) : RawOutcome F input .ct4
  | c1 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (certificate : C1Certificate F input dormant) : RawOutcome F input .c1
  | ct3 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT3Payload F input dormant) : RawOutcome F input .ct3
  | ct7 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT7Payload F input dormant) : RawOutcome F input .ct7
  | ct9 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT9Payload F input dormant) : RawOutcome F input .ct9
  | ct10 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT10Payload F input dormant) : RawOutcome F input .ct10

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

def runCore (F : Framework) (input : Input F)
    (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope,
        .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scopeState =>
      let definition := Nodes.Definition.run plan.definition scopeState
      match Nodes.Activity.run plan.activity definition with
      | .active active =>
          let payload := Nodes.ActiveLedger.run plan.activeLedger active
          ⟨.ct4,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.definitionCertified definition)
                  (.cons (.activityActive active)
                    (.cons (.activeLedgerToCT4 payload) (.nil .ct4Terminal))))),
            .ct4 payload⟩
      | .dormant dormant =>
          match Nodes.Dormant.run plan.dormant dormant with
          | .close certificate =>
              ⟨.c1,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.definitionCertified definition)
                      (.cons (.activityDormant dormant)
                        (.cons (.dormantClose certificate) (.nil .c1Terminal))))),
                .c1 certificate⟩
          | .toCT3 payload =>
              ⟨.ct3,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.definitionCertified definition)
                      (.cons (.activityDormant dormant)
                        (.cons (.dormantToCT3 payload) (.nil .ct3Terminal))))),
                .ct3 payload⟩
          | .toCT7 payload =>
              ⟨.ct7,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.definitionCertified definition)
                      (.cons (.activityDormant dormant)
                        (.cons (.dormantToCT7 payload) (.nil .ct7Terminal))))),
                .ct7 payload⟩
          | .toCT9 payload =>
              ⟨.ct9,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.definitionCertified definition)
                      (.cons (.activityDormant dormant)
                        (.cons (.dormantToCT9 payload) (.nil .ct9Terminal))))),
                .ct9 payload⟩
          | .toCT10 payload =>
              ⟨.ct10,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.definitionCertified definition)
                      (.cons (.activityDormant dormant)
                        (.cons (.dormantToCT10 payload) (.nil .ct10Terminal))))),
                .ct10 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct4 {definition : DefinitionState F input}
      {active : ActiveState F input definition}
      (payload : CT4Payload F input active)
      (accepted : port.accepts (.ct4 payload)) : Outcome F input port .ct4
  | c1 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (certificate : C1Certificate F input dormant) : Outcome F input port .c1
  | ct3 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT3Payload F input dormant)
      (accepted : port.accepts (.ct3 payload)) : Outcome F input port .ct3
  | ct7 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT7Payload F input dormant)
      (accepted : port.accepts (.ct7 payload)) : Outcome F input port .ct7
  | ct9 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT9Payload F input dormant)
      (accepted : port.accepts (.ct9 payload)) : Outcome F input port .ct9
  | ct10 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT10Payload F input dormant)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct4 payload _ => port.accepts (.ct4 payload)
  | .c1 _ => F.entry.C1Claim input.G input.branch
  | .ct3 payload _ => port.accepts (.ct3 payload)
  | .ct7 payload _ => port.accepts (.ct7 payload)
  | .ct9 payload _ => port.accepts (.ct9 payload)
  | .ct10 payload _ => port.accepts (.ct10 payload)

structure ExecutionResult (F : Framework) (input : Input F)
    (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal

namespace ExecutionResult

def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId := result.path.trace

end ExecutionResult

def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port)
    (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ => ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .ct4 payload⟩ =>
      ⟨.ct4, path, .ct4 payload (handoff.accept (.ct4 payload))⟩
  | ⟨_, path, .c1 certificate⟩ => ⟨.c1, path, .c1 certificate⟩
  | ⟨_, path, .ct3 payload⟩ =>
      ⟨.ct3, path, .ct3 payload (handoff.accept (.ct3 payload))⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩
  | ⟨_, path, .ct9 payload⟩ =>
      ⟨.ct9, path, .ct9 payload (handoff.accept (.ct9 payload))⟩
  | ⟨_, path, .ct10 payload⟩ =>
      ⟨.ct10, path, .ct10 payload (handoff.accept (.ct10 payload))⟩

def runTraced (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)

def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal

def run (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT6
