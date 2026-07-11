import StructuralExhaustion.CT7.Nodes
import StructuralExhaustion.CT7.Graph

namespace StructuralExhaustion.CT7

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  context : Nodes.Context.Plan F input
  realization : Nodes.Realization.Plan F input
  distinction : Nodes.Distinction.Plan F input
  defect : Nodes.Defect.Plan F input
  neutral : Nodes.Neutral.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | c1 {context : ContextState F input}
      (certificate : C1Certificate F input context) : RawOutcome F input .c1
  | c3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (certificate : C3Certificate F input defect) : RawOutcome F input .c3
  | ct3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT3Payload F input defect) : RawOutcome F input .ct3
  | ct12 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT12Payload F input defect) : RawOutcome F input .ct12
  | c2 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (certificate : C2Certificate F input neutral) : RawOutcome F input .c2
  | ct10 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT10Payload F input neutral) : RawOutcome F input .ct10
  | ct16 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT16Payload F input neutral) : RawOutcome F input .ct16

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

def runCore (F : Framework) (input : Input F)
    (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scopeState =>
      let context := Nodes.Context.run plan.context scopeState
      match Nodes.Realization.run plan.realization context with
      | .close certificate =>
          ⟨.c1,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.contextCertified context)
                  (.cons (.realizationClose certificate) (.nil .c1Terminal)))),
            .c1 certificate⟩
      | .unrealized unrealized =>
          match Nodes.Distinction.run plan.distinction unrealized with
          | .defect defect =>
              match Nodes.Defect.run plan.defect defect with
              | .close certificate =>
                  ⟨.c3,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionDefect defect)
                              (.cons (.defectClose certificate) (.nil .c3Terminal)))))),
                    .c3 certificate⟩
              | .toCT3 payload =>
                  ⟨.ct3,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionDefect defect)
                              (.cons (.defectToCT3 payload) (.nil .ct3Terminal)))))),
                    .ct3 payload⟩
              | .toCT12 payload =>
                  ⟨.ct12,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionDefect defect)
                              (.cons (.defectToCT12 payload) (.nil .ct12Terminal)))))),
                    .ct12 payload⟩
          | .neutral neutral =>
              match Nodes.Neutral.run plan.neutral neutral with
              | .close certificate =>
                  ⟨.c2,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionNeutral neutral)
                              (.cons (.neutralClose certificate) (.nil .c2Terminal)))))),
                    .c2 certificate⟩
              | .toCT10 payload =>
                  ⟨.ct10,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionNeutral neutral)
                              (.cons (.neutralToCT10 payload) (.nil .ct10Terminal)))))),
                    .ct10 payload⟩
              | .toCT16 payload =>
                  ⟨.ct16,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.contextCertified context)
                          (.cons (.realizationUnrealized unrealized)
                            (.cons (.distinctionNeutral neutral)
                              (.cons (.neutralToCT16 payload) (.nil .ct16Terminal)))))),
                    .ct16 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | c1 {context : ContextState F input}
      (certificate : C1Certificate F input context) : Outcome F input port .c1
  | c3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (certificate : C3Certificate F input defect) : Outcome F input port .c3
  | ct3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT3Payload F input defect)
      (accepted : port.accepts (.ct3 payload)) : Outcome F input port .ct3
  | ct12 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT12Payload F input defect)
      (accepted : port.accepts (.ct12 payload)) : Outcome F input port .ct12
  | c2 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (certificate : C2Certificate F input neutral) : Outcome F input port .c2
  | ct10 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT10Payload F input neutral)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10
  | ct16 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT16Payload F input neutral)
      (accepted : port.accepts (.ct16 payload)) : Outcome F input port .ct16

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .c1 _ => F.entry.C1Claim input.G input.branch
  | .c3 _ => F.entry.C3Claim input.G input.branch
  | .ct3 payload _ => port.accepts (.ct3 payload)
  | .ct12 payload _ => port.accepts (.ct12 payload)
  | .c2 _ => F.entry.C2Claim input.G input.branch
  | .ct10 payload _ => port.accepts (.ct10 payload)
  | .ct16 payload _ => port.accepts (.ct16 payload)

structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
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
  | ⟨_, path, .c1 certificate⟩ => ⟨.c1, path, .c1 certificate⟩
  | ⟨_, path, .c3 certificate⟩ => ⟨.c3, path, .c3 certificate⟩
  | ⟨_, path, .ct3 payload⟩ =>
      ⟨.ct3, path, .ct3 payload (handoff.accept (.ct3 payload))⟩
  | ⟨_, path, .ct12 payload⟩ =>
      ⟨.ct12, path, .ct12 payload (handoff.accept (.ct12 payload))⟩
  | ⟨_, path, .c2 certificate⟩ => ⟨.c2, path, .c2 certificate⟩
  | ⟨_, path, .ct10 payload⟩ =>
      ⟨.ct10, path, .ct10 payload (handoff.accept (.ct10 payload))⟩
  | ⟨_, path, .ct16 payload⟩ =>
      ⟨.ct16, path, .ct16 payload (handoff.accept (.ct16 payload))⟩

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

end StructuralExhaustion.CT7
