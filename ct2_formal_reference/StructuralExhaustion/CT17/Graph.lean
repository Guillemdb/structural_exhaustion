import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Graph
inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | compatibilityDecision
  | separationDecision
  | ct3Terminal
  | ct10Terminal
  | blockCertification
  | scaleDecision
  | survivorsDecision
  | c5Terminal
  | ct8Terminal
  | arithmeticDecision
  | c1Terminal
  | ct14Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT17.entry" | .scopeDecision => "CT17.decide.scope"
  | .scopeTerminal => "CT17.terminal.scope"
  | .compatibilityDecision => "CT17.decide.compatibility"
  | .separationDecision => "CT17.decide.separation"
  | .ct3Terminal => "CT17.terminal.ct3" | .ct10Terminal => "CT17.terminal.ct10"
  | .blockCertification => "CT17.certify.block" | .scaleDecision => "CT17.decide.scale"
  | .survivorsDecision => "CT17.decide.survivors" | .c5Terminal => "CT17.terminal.c5"
  | .ct8Terminal => "CT17.terminal.ct8" | .arithmeticDecision => "CT17.decide.arithmetic"
  | .c1Terminal => "CT17.terminal.c1" | .ct14Terminal => "CT17.terminal.ct14"
end NodeId
inductive Terminal where
  | scope
  | ct3
  | ct10
  | c5
  | ct8
  | c1
  | ct14
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct3 => .ct3Terminal | .ct10 => .ct10Terminal
  | .c5 => .c5Terminal | .ct8 => .ct8Terminal | .c1 => .c1Terminal
  | .ct14 => .ct14Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeReady (scope : ScopedState F input) : Edge F input .scopeDecision .compatibilityDecision
  | compatibilityYes {scope : ScopedState F input} (state : CompatibleState F input scope) :
      Edge F input .compatibilityDecision .blockCertification
  | compatibilityNo {scope : ScopedState F input} (state : IncompatibleState F input scope) :
      Edge F input .compatibilityDecision .separationDecision
  | separationToCT3 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT3Payload F input state) : Edge F input .separationDecision .ct3Terminal
  | separationToCT10 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT10Payload F input state) : Edge F input .separationDecision .ct10Terminal
  | blockCertified {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      (block : BlockState F input compatible) : Edge F input .blockCertification .scaleDecision
  | scaleFinite {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} (finite : FiniteState F input block) :
      Edge F input .scaleDecision .survivorsDecision
  | scaleRepeated {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} (repeated : RepeatedState F input block) :
      Edge F input .scaleDecision .arithmeticDecision
  | survivorsExhausted {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (certificate : C5Certificate F input finite) : Edge F input .survivorsDecision .c5Terminal
  | survivorsToCT8 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (payload : CT8Payload F input finite) : Edge F input .survivorsDecision .ct8Terminal
  | arithmeticClose {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (certificate : C1Certificate F input repeated) : Edge F input .arithmeticDecision .c1Terminal
  | arithmeticToCT14 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (payload : CT14Payload F input repeated) : Edge F input .arithmeticDecision .ct14Terminal
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
  ∃ terminal : Terminal, ∃ path : Path F input .entry terminal.nodeId, path.trace = nodes
end StructuralExhaustion.CT17.Graph
