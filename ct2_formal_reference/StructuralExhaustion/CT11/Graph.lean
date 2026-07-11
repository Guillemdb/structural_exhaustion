import StructuralExhaustion.CT11.Types

namespace StructuralExhaustion.CT11.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | decompositionCertification
  | admissibilityDecision
  | ct10Terminal
  | localizationCertification
  | routingDecision
  | ct1Terminal
  | ct7Terminal
  | ct14Terminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT11.entry"
  | .scopeDecision => "CT11.decide.scope"
  | .scopeTerminal => "CT11.terminal.scope"
  | .decompositionCertification => "CT11.certify.decomposition"
  | .admissibilityDecision => "CT11.decide.admissibility"
  | .ct10Terminal => "CT11.terminal.ct10"
  | .localizationCertification => "CT11.certify.localization"
  | .routingDecision => "CT11.decide.routing"
  | .ct1Terminal => "CT11.terminal.ct1"
  | .ct7Terminal => "CT11.terminal.ct7"
  | .ct14Terminal => "CT11.terminal.ct14"
end NodeId

inductive Terminal where
  | scope
  | ct10
  | ct1
  | ct7
  | ct14
  deriving Repr, DecidableEq

namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .ct10 => .ct10Terminal
  | .ct1 => .ct1Terminal
  | .ct7 => .ct7Terminal
  | .ct14 => .ct14Terminal
end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .decompositionCertification
  | decompositionCertified (state : DecompositionState F input) :
      Edge F input .decompositionCertification .admissibilityDecision
  | admissibilityRefine {decomposition : DecompositionState F input}
      (payload : CT10Payload F input decomposition) :
      Edge F input .admissibilityDecision .ct10Terminal
  | admissibilityClosed {decomposition : DecompositionState F input}
      (state : AdmissibleState F input decomposition) :
      Edge F input .admissibilityDecision .localizationCertification
  | localizationCertified {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      (state : LocalizationState F input admissible) :
      Edge F input .localizationCertification .routingDecision
  | routingToCT1 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT1Payload F input localized) :
      Edge F input .routingDecision .ct1Terminal
  | routingToCT7 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT7Payload F input localized) :
      Edge F input .routingDecision .ct7Terminal
  | routingToCT14 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT14Payload F input localized) :
      Edge F input .routingDecision .ct14Terminal

namespace Edge
def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src
end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} : Edge F input first second →
      Path F input second last → Path F input first last

namespace Path
def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path

def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path F input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT11.Graph
