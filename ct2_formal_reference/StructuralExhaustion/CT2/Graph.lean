import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Graph

/-!
The semantic CT2 graph.  `Edge` is not a diagram-only adjacency relation: each
nontrivial constructor carries the evidence produced by the corresponding node.
Consequently, a `Path` is an execution certificate, not merely a list of labels.
-/

inductive NodeId where
  | entry
  | interfaceDecision
  | deletionDecision
  | replacementCandidateSearch
  | candidateContextCertification
  | survivorClassification
  | scopeTerminal
  | deletionC2Terminal
  | contextCT3Terminal
  | replacementC2Terminal
  | criticalityCT10Terminal
  | responseCT3Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT2.entry"
  | .interfaceDecision => "CT2.decide.interface"
  | .deletionDecision => "CT2.decide.deletion"
  | .replacementCandidateSearch => "CT2.decide.replacementCandidate"
  | .candidateContextCertification => "CT2.decide.context"
  | .survivorClassification => "CT2.decide.survivor"
  | .scopeTerminal => "CT2.terminal.scope"
  | .deletionC2Terminal => "CT2.terminal.c2.deletion"
  | .contextCT3Terminal => "CT2.terminal.ct3.context"
  | .replacementC2Terminal => "CT2.terminal.c2.replacement"
  | .criticalityCT10Terminal => "CT2.terminal.ct10.criticality"
  | .responseCT3Terminal => "CT2.terminal.ct3.response"

end NodeId

inductive Terminal where
  | scope
  | deletionC2
  | contextCT3
  | replacementC2
  | criticalityCT10
  | responseCT3
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .deletionC2 => .deletionC2Terminal
  | .contextCT3 => .contextCT3Terminal
  | .replacementC2 => .replacementC2Terminal
  | .criticalityCT10 => .criticalityCT10Terminal
  | .responseCT3 => .responseCT3Terminal

end Terminal

/-- Evidence-carrying transitions of the CT2 machine. -/
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginInterface :
      Edge F input .entry .interfaceDecision
  | interfaceScope
      (candidate : ScopeCandidate F input) :
      Edge F input .interfaceDecision .scopeTerminal
  | interfaceBounded
      (state : BoundedState F input) :
      Edge F input .interfaceDecision .deletionDecision
  | deletionCloses
      (witness : DeletionWitness F input) :
      Edge F input .deletionDecision .deletionC2Terminal
  | deletionCritical
      (state : DeletionCriticalState F input) :
      Edge F input .deletionDecision .replacementCandidateSearch
  | candidateFound
      (state : CandidateState F input) :
      Edge F input
        .replacementCandidateSearch .candidateContextCertification
  | candidateAbsent
      (state : SurvivorState F input) :
      Edge F input .replacementCandidateSearch .survivorClassification
  | contextCertified
      (state : CandidateState F input)
      (certificate : CandidateContextCertificate F input state) :
      Edge F input
        .candidateContextCertification .replacementC2Terminal
  | contextResidual
      {state : CandidateState F input}
      (payload : ContextCT3Payload F input state) :
      Edge F input .candidateContextCertification .contextCT3Terminal
  | survivorCriticality
      {survivor : SurvivorState F input}
      (payload : CriticalityCT10Payload F input survivor) :
      Edge F input .survivorClassification .criticalityCT10Terminal
  | survivorMissingResponse
      {survivor : SurvivorState F input}
      (payload : ResponseCT3Payload F input survivor) :
      Edge F input .survivorClassification .responseCT3Terminal

namespace Edge

def source {F : Framework} {input : Input F} {start finish : NodeId}
    (_edge : Edge F input start finish) : NodeId := start

def target {F : Framework} {input : Input F} {start finish : NodeId}
    (_edge : Edge F input start finish) : NodeId := finish

end Edge

/-- A dependent path whose indices enforce exact edge composition. -/
inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} :
      Edge F input first second →
      Path F input second last →
      Path F input first last

namespace Path

def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

/-- An erased node list is valid exactly when it is backed by a typed path from
the semantic entry node to one of the six terminals. -/
def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path F input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT2.Graph
