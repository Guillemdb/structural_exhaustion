import StructuralExhaustion.CT1.Graph
import StructuralExhaustion.CT1.Nodes

namespace StructuralExhaustion.CT1

/-- Core mathematical implementations, one field per non-entry semantic node. -/
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  equivalence : Nodes.Equivalence.Plan F input
  realization : Nodes.Realization.Plan F input
  payload : Nodes.Payload.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) :
      RawOutcome F input .scope
  | c1 (certificate : C1Certificate F input) :
      RawOutcome F input .c1
  | ct2 {avoiding : AvoidingState F input}
      (payload : CT2Payload F input avoiding) :
      RawOutcome F input .ct2
  | ct3 {avoiding : AvoidingState F input}
      (payload : CT3Payload F input avoiding) :
      RawOutcome F input .ct3
  | ct4 {avoiding : AvoidingState F input}
      (payload : CT4Payload F input avoiding) :
      RawOutcome F input .ct4
  | ct5 {avoiding : AvoidingState F input}
      (payload : CT5Payload F input avoiding) :
      RawOutcome F input .ct5
  | ct6 {avoiding : AvoidingState F input}
      (payload : CT6Payload F input avoiding) :
      RawOutcome F input .ct6
  | ct17 {avoiding : AvoidingState F input}
      (payload : CT17Payload F input avoiding) :
      RawOutcome F input .ct17

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

namespace CoreResult

def trace {F : Framework} {input : Input F}
    (result : CoreResult F input) : List Graph.NodeId :=
  result.path.trace

end CoreResult

def runCore (F : Framework) (input : Input F)
    (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      {
        terminal := .scope
        path := .cons .beginScope
          (.cons (.scopeExit candidate) (.nil .scopeTerminal))
        outcome := .scope candidate
      }
  | .ready scopeState =>
      let equivalence := Nodes.Equivalence.run plan.equivalence scopeState
      match Nodes.Realization.run plan.realization equivalence with
      | .hit certificate =>
          {
            terminal := .c1
            path := .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.equivalenceCertified equivalence)
                  (.cons (.realizationHit certificate)
                    (.nil .c1Terminal))))
            outcome := .c1 certificate
          }
      | .avoiding avoiding =>
          match Nodes.Payload.run plan.payload avoiding with
          | .toCT2 payload =>
              {
                terminal := .ct2
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT2 payload)
                          (.nil .ct2Terminal)))))
                outcome := .ct2 payload
              }
          | .toCT3 payload =>
              {
                terminal := .ct3
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT3 payload)
                          (.nil .ct3Terminal)))))
                outcome := .ct3 payload
              }
          | .toCT4 payload =>
              {
                terminal := .ct4
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT4 payload)
                          (.nil .ct4Terminal)))))
                outcome := .ct4 payload
              }
          | .toCT5 payload =>
              {
                terminal := .ct5
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT5 payload)
                          (.nil .ct5Terminal)))))
                outcome := .ct5 payload
              }
          | .toCT6 payload =>
              {
                terminal := .ct6
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT6 payload)
                          (.nil .ct6Terminal)))))
                outcome := .ct6 payload
              }
          | .toCT17 payload =>
              {
                terminal := .ct17
                path := .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.realizationAvoiding avoiding)
                        (.cons (.payloadToCT17 payload)
                          (.nil .ct17Terminal)))))
                outcome := .ct17 payload
              }

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) :
      Outcome F input port .scope
  | c1 (certificate : C1Certificate F input) :
      Outcome F input port .c1
  | ct2 {avoiding : AvoidingState F input}
      (payload : CT2Payload F input avoiding)
      (accepted : port.accepts (.ct2 payload)) :
      Outcome F input port .ct2
  | ct3 {avoiding : AvoidingState F input}
      (payload : CT3Payload F input avoiding)
      (accepted : port.accepts (.ct3 payload)) :
      Outcome F input port .ct3
  | ct4 {avoiding : AvoidingState F input}
      (payload : CT4Payload F input avoiding)
      (accepted : port.accepts (.ct4 payload)) :
      Outcome F input port .ct4
  | ct5 {avoiding : AvoidingState F input}
      (payload : CT5Payload F input avoiding)
      (accepted : port.accepts (.ct5 payload)) :
      Outcome F input port .ct5
  | ct6 {avoiding : AvoidingState F input}
      (payload : CT6Payload F input avoiding)
      (accepted : port.accepts (.ct6 payload)) :
      Outcome F input port .ct6
  | ct17 {avoiding : AvoidingState F input}
      (payload : CT17Payload F input avoiding)
      (accepted : port.accepts (.ct17 payload)) :
      Outcome F input port .ct17

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .c1 _ => F.ct2.Target input.G
  | .ct2 payload _ => port.accepts (.ct2 payload)
  | .ct3 payload _ => port.accepts (.ct3 payload)
  | .ct4 payload _ => port.accepts (.ct4 payload)
  | .ct5 payload _ => port.accepts (.ct5 payload)
  | .ct6 payload _ => port.accepts (.ct6 payload)
  | .ct17 payload _ => port.accepts (.ct17 payload)

structure ExecutionResult (F : Framework) (input : Input F)
    (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal

namespace ExecutionResult

def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port)
    (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ =>
      ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .c1 certificate⟩ =>
      ⟨.c1, path, .c1 certificate⟩
  | ⟨_, path, .ct2 payload⟩ =>
      ⟨.ct2, path, .ct2 payload (handoff.accept (.ct2 payload))⟩
  | ⟨_, path, .ct3 payload⟩ =>
      ⟨.ct3, path, .ct3 payload (handoff.accept (.ct3 payload))⟩
  | ⟨_, path, .ct4 payload⟩ =>
      ⟨.ct4, path, .ct4 payload (handoff.accept (.ct4 payload))⟩
  | ⟨_, path, .ct5 payload⟩ =>
      ⟨.ct5, path, .ct5 payload (handoff.accept (.ct5 payload))⟩
  | ⟨_, path, .ct6 payload⟩ =>
      ⟨.ct6, path, .ct6 payload (handoff.accept (.ct6 payload))⟩
  | ⟨_, path, .ct17 payload⟩ =>
      ⟨.ct17, path, .ct17 payload (handoff.accept (.ct17 payload))⟩

def runTraced (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) :
    ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)

def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal

def run (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT1
