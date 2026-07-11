import StructuralExhaustion.CT11.Nodes
import StructuralExhaustion.CT11.Graph

namespace StructuralExhaustion.CT11

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  decomposition : Nodes.Decomposition.Plan F input
  admissibility : Nodes.Admissibility.Plan F input
  localization : Nodes.Localization.Plan F input
  routing : Nodes.Routing.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct10 {decomposition : DecompositionState F input}
      (payload : CT10Payload F input decomposition) : RawOutcome F input .ct10
  | ct1 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT1Payload F input localized) : RawOutcome F input .ct1
  | ct7 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT7Payload F input localized) : RawOutcome F input .ct7
  | ct14 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT14Payload F input localized) : RawOutcome F input .ct14

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) :
    CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope,
        .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scopeState =>
      let decomposition := Nodes.Decomposition.run plan.decomposition scopeState
      match Nodes.Admissibility.run plan.admissibility decomposition with
      | .refine payload =>
          ⟨.ct10,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.decompositionCertified decomposition)
                  (.cons (.admissibilityRefine payload) (.nil .ct10Terminal)))),
            .ct10 payload⟩
      | .closed admissible =>
          let localized := Nodes.Localization.run plan.localization admissible
          match Nodes.Routing.run plan.routing localized with
          | .toCT1 payload =>
              ⟨.ct1,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.decompositionCertified decomposition)
                      (.cons (.admissibilityClosed admissible)
                        (.cons (.localizationCertified localized)
                          (.cons (.routingToCT1 payload) (.nil .ct1Terminal)))))),
                .ct1 payload⟩
          | .toCT7 payload =>
              ⟨.ct7,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.decompositionCertified decomposition)
                      (.cons (.admissibilityClosed admissible)
                        (.cons (.localizationCertified localized)
                          (.cons (.routingToCT7 payload) (.nil .ct7Terminal)))))),
                .ct7 payload⟩
          | .toCT14 payload =>
              ⟨.ct14,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.decompositionCertified decomposition)
                      (.cons (.admissibilityClosed admissible)
                        (.cons (.localizationCertified localized)
                          (.cons (.routingToCT14 payload) (.nil .ct14Terminal)))))),
                .ct14 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct10 {decomposition : DecompositionState F input}
      (payload : CT10Payload F input decomposition)
      (accepted : port.accepts (.ct10 payload)) : Outcome F input port .ct10
  | ct1 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT1Payload F input localized)
      (accepted : port.accepts (.ct1 payload)) : Outcome F input port .ct1
  | ct7 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT7Payload F input localized)
      (accepted : port.accepts (.ct7 payload)) : Outcome F input port .ct7
  | ct14 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT14Payload F input localized)
      (accepted : port.accepts (.ct14 payload)) : Outcome F input port .ct14

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct10 payload _ => port.accepts (.ct10 payload)
  | .ct1 payload _ => port.accepts (.ct1 payload)
  | .ct7 payload _ => port.accepts (.ct7 payload)
  | .ct14 payload _ => port.accepts (.ct14 payload)

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
  | ⟨_, path, .ct1 payload⟩ =>
      ⟨.ct1, path, .ct1 payload (handoff.accept (.ct1 payload))⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩
  | ⟨_, path, .ct14 payload⟩ =>
      ⟨.ct14, path, .ct14 payload (handoff.accept (.ct14 payload))⟩

def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)

def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal

def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT11
