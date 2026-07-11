import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | ct10Terminal
  | equivalenceCertification
  | repetitionDecision
  | c5Terminal
  | responseDecision
  | c2Terminal
  | routingDecision
  | ct3Terminal
  | ct7Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT8.entry"
  | .scopeDecision => "CT8.decide.scope"
  | .scopeTerminal => "CT8.terminal.scope"
  | .ct10Terminal => "CT8.terminal.ct10"
  | .equivalenceCertification => "CT8.certify.equivalence"
  | .repetitionDecision => "CT8.decide.repetition"
  | .c5Terminal => "CT8.terminal.c5"
  | .responseDecision => "CT8.decide.response"
  | .c2Terminal => "CT8.terminal.c2"
  | .routingDecision => "CT8.decide.routing"
  | .ct3Terminal => "CT8.terminal.ct3"
  | .ct7Terminal => "CT8.terminal.ct7"
end NodeId

inductive Terminal where
  | scope
  | ct10
  | c5
  | c2
  | ct3
  | ct7
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct10 => .ct10Terminal | .c5 => .c5Terminal
  | .c2 => .c2Terminal | .ct3 => .ct3Terminal | .ct7 => .ct7Terminal
end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeRefine (payload : CT10Payload F input) :
      Edge F input .scopeDecision .ct10Terminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .equivalenceCertification
  | equivalenceCertified (state : EqualityState F input) :
      Edge F input .equivalenceCertification .repetitionDecision
  | repetitionShort {equality : EqualityState F input}
      (certificate : C5Certificate F input equality) :
      Edge F input .repetitionDecision .c5Terminal
  | repetitionRepeated {equality : EqualityState F input}
      (state : RepeatedState F input equality) :
      Edge F input .repetitionDecision .responseDecision
  | responseClose {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      (certificate : C2Certificate F input repeated) :
      Edge F input .responseDecision .c2Terminal
  | responseSeparating {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      (state : SeparatingState F input repeated) :
      Edge F input .responseDecision .routingDecision
  | routingToCT3 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT3Payload F input separating) :
      Edge F input .routingDecision .ct3Terminal
  | routingToCT7 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT7Payload F input separating) :
      Edge F input .routingDecision .ct7Terminal
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
end StructuralExhaustion.CT8.Graph
