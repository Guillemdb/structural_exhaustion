import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Graph
inductive NodeId where
  | entry
  | supportDecision
  | ct3Terminal
  | scopeDecision
  | scopeTerminal
  | closedTypeCertification
  | equalityDecision
  | c2Terminal
  | ct10Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT16.entry" | .supportDecision => "CT16.decide.support"
  | .ct3Terminal => "CT16.terminal.ct3" | .scopeDecision => "CT16.decide.scope"
  | .scopeTerminal => "CT16.terminal.scope"
  | .closedTypeCertification => "CT16.certify.closedType"
  | .equalityDecision => "CT16.decide.equality" | .c2Terminal => "CT16.terminal.c2"
  | .ct10Terminal => "CT16.terminal.ct10"
end NodeId
inductive Terminal where
  | ct3
  | scope
  | c2
  | ct10
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .ct3 => .ct3Terminal | .scope => .scopeTerminal
  | .c2 => .c2Terminal | .ct10 => .ct10Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginSupport : Edge F input .entry .supportDecision
  | supportProper {proper : ProperState F input} (payload : CT3Payload F input proper) :
      Edge F input .supportDecision .ct3Terminal
  | supportWhole (whole : WholeState F input) : Edge F input .supportDecision .scopeDecision
  | scopeExit (whole : WholeState F input) (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady {whole : WholeState F input} (scope : ScopedState F input whole) :
      Edge F input .scopeDecision .closedTypeCertification
  | closedTypeCertified {whole : WholeState F input} {scope : ScopedState F input whole}
      (closed : ClosedTypeState F input scope) :
      Edge F input .closedTypeCertification .equalityDecision
  | equalityClose {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (certificate : C2Certificate F input closed) :
      Edge F input .equalityDecision .c2Terminal
  | equalityDistinct {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (payload : CT10Payload F input closed) :
      Edge F input .equalityDecision .ct10Terminal
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
end StructuralExhaustion.CT16.Graph
