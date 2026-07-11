import StructuralExhaustion.CT2.Graph
import StructuralExhaustion.CT2.Nodes

namespace StructuralExhaustion.CT2

/-- The five independent core decision providers.  Consumer acceptance is kept
out of this record and supplied separately through `Port` and `HandoffPlan`. -/
structure CorePlan (F : Framework) (input : Input F) where
  interface : Nodes.Interface.Plan F input
  deletion : Nodes.Deletion.Plan F input
  replacementCandidate : Nodes.ReplacementCandidate.Plan F input
  context : Nodes.Context.Plan F input
  survivor : Nodes.Survivor.Plan F input

/-- Uncertified terminal data produced by the core CT2 machine.  Each
constructor is indexed by one exact semantic terminal. -/
inductive RawOutcome (F : Framework) (input : Input F) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) :
      RawOutcome F input .scope
  | deletionC2 (witness : DeletionWitness F input) :
      RawOutcome F input .deletionC2
  | contextCT3 {state : CandidateState F input}
      (payload : ContextCT3Payload F input state) :
      RawOutcome F input .contextCT3
  | replacementC2
      (state : CandidateState F input)
      (certificate : CandidateContextCertificate F input state) :
      RawOutcome F input .replacementC2
  | criticalityCT10 {survivor : SurvivorState F input}
      (payload : CriticalityCT10Payload F input survivor) :
      RawOutcome F input .criticalityCT10
  | responseCT3 {survivor : SurvivorState F input}
      (payload : ResponseCT3Payload F input survivor) :
      RawOutcome F input .responseCT3

/-- Core execution returns a semantic terminal, its evidence-carrying path, and
the raw terminal data indexed by the same terminal. -/
structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

namespace CoreResult

def trace {F : Framework} {input : Input F}
    (result : CoreResult F input) : List Graph.NodeId :=
  result.path.trace

end CoreResult

/-- Execute only the mathematical CT2 decisions.  Every match invokes the
corresponding semantic node API, and every selected edge stores that node's
complete output evidence. -/
def runCore (F : Framework) (input : Input F)
    (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Interface.run entry plan.interface with
  | .scope candidate =>
      {
        terminal := .scope
        path := .cons .beginInterface
          (.cons (.interfaceScope candidate) (.nil .scopeTerminal))
        outcome := .scope candidate
      }
  | .bounded bounded =>
      match Nodes.Deletion.run plan.deletion bounded with
      | .closes witness =>
          {
            terminal := .deletionC2
            path := .cons .beginInterface
              (.cons (.interfaceBounded bounded)
                (.cons (.deletionCloses witness)
                  (.nil .deletionC2Terminal)))
            outcome := .deletionC2 witness
          }
      | .critical critical =>
          match Nodes.ReplacementCandidate.run
              plan.replacementCandidate critical with
          | .found candidate =>
              match Nodes.Context.run plan.context candidate with
              | .certified certificate =>
                  {
                    terminal := .replacementC2
                    path := .cons .beginInterface
                      (.cons (.interfaceBounded bounded)
                        (.cons (.deletionCritical critical)
                          (.cons (.candidateFound candidate)
                            (.cons
                              (.contextCertified candidate certificate)
                              (.nil .replacementC2Terminal)))))
                    outcome := .replacementC2 candidate certificate
                  }
              | .residual payload =>
                  {
                    terminal := .contextCT3
                    path := .cons .beginInterface
                      (.cons (.interfaceBounded bounded)
                        (.cons (.deletionCritical critical)
                          (.cons (.candidateFound candidate)
                            (.cons (.contextResidual payload)
                              (.nil .contextCT3Terminal)))))
                    outcome := .contextCT3 payload
                  }
          | .absent survivor =>
              match Nodes.Survivor.run plan.survivor survivor with
              | .criticality payload =>
                  {
                    terminal := .criticalityCT10
                    path := .cons .beginInterface
                      (.cons (.interfaceBounded bounded)
                        (.cons (.deletionCritical critical)
                          (.cons (.candidateAbsent survivor)
                            (.cons (.survivorCriticality payload)
                              (.nil .criticalityCT10Terminal)))))
                    outcome := .criticalityCT10 payload
                  }
              | .missingResponse payload =>
                  {
                    terminal := .responseCT3
                    path := .cons .beginInterface
                      (.cons (.interfaceBounded bounded)
                        (.cons (.deletionCritical critical)
                          (.cons (.candidateAbsent survivor)
                            (.cons (.survivorMissingResponse payload)
                              (.nil .responseCT3Terminal)))))
                    outcome := .responseCT3 payload
                  }

/-- Consumer-certified terminal outcome, indexed by the exact terminal. -/
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) :
      Outcome F input port .scope
  | deletionC2 (witness : DeletionWitness F input) :
      Outcome F input port .deletionC2
  | contextCT3 {state : CandidateState F input}
      (payload : ContextCT3Payload F input state)
      (accepted : port.ct3Accepts (.context payload)) :
      Outcome F input port .contextCT3
  | replacementC2
      (state : CandidateState F input)
      (certificate : CandidateContextCertificate F input state) :
      Outcome F input port .replacementC2
  | criticalityCT10 {survivor : SurvivorState F input}
      (payload : CriticalityCT10Payload F input survivor)
      (accepted : port.ct10Accepts (.criticality payload)) :
      Outcome F input port .criticalityCT10
  | responseCT3 {survivor : SurvivorState F input}
      (payload : ResponseCT3Payload F input survivor)
      (accepted : port.ct3Accepts (.missingResponse payload)) :
      Outcome F input port .responseCT3

/-- The proposition established by each terminal. -/
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ InterfaceBoundedAt F input
  | .deletionC2 _ => False
  | .contextCT3 payload _ => port.ct3Accepts (.context payload)
  | .replacementC2 _ _ => False
  | .criticalityCT10 payload _ => port.ct10Accepts (.criticality payload)
  | .responseCT3 payload _ => port.ct3Accepts (.missingResponse payload)

/-- A certified run preserves the core path and adds only consumer acceptance
proofs at routed terminals. -/
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

/-- Certify only the downstream handoff part of a core result. -/
def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port)
    (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ =>
      ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .deletionC2 witness⟩ =>
      ⟨.deletionC2, path, .deletionC2 witness⟩
  | ⟨_, path, .contextCT3 payload⟩ =>
      ⟨.contextCT3, path,
        .contextCT3 payload (handoff.acceptCT3 (.context payload))⟩
  | ⟨_, path, .replacementC2 state certificate⟩ =>
      ⟨.replacementC2, path, .replacementC2 state certificate⟩
  | ⟨_, path, .criticalityCT10 payload⟩ =>
      ⟨.criticalityCT10, path,
        .criticalityCT10 payload (handoff.acceptCT10 (.criticality payload))⟩
  | ⟨_, path, .responseCT3 payload⟩ =>
      ⟨.responseCT3, path,
        .responseCT3 payload (handoff.acceptCT3 (.missingResponse payload))⟩

/-- Full traced execution with the core plan and handoff plan visibly separate. -/
def runTraced (F : Framework) (input : Input F)
    (plan : CorePlan F input)
    (port : Port F input)
    (handoff : HandoffPlan F input port) :
    ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)

/-- Existential outcome-only view for callers that do not need the path. -/
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal

def run (F : Framework) (input : Input F)
    (plan : CorePlan F input)
    (port : Port F input)
    (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT2
