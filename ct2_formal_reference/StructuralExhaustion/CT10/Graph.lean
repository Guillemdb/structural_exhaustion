import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Graph
inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | labelCertification
  | classificationDecision
  | c5Terminal
  | directDecision
  | ct3Terminal
  | ct7Terminal
  | promotionCertification
  | promotedRoutingDecision
  | ct15Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT10.entry"
  | .scopeDecision => "CT10.decide.scope"
  | .scopeTerminal => "CT10.terminal.scope"
  | .labelCertification => "CT10.certify.labels"
  | .classificationDecision => "CT10.decide.classification"
  | .c5Terminal => "CT10.terminal.c5"
  | .directDecision => "CT10.decide.direct"
  | .ct3Terminal => "CT10.terminal.ct3"
  | .ct7Terminal => "CT10.terminal.ct7"
  | .promotionCertification => "CT10.certify.promotion"
  | .promotedRoutingDecision => "CT10.decide.promotedRouting"
  | .ct15Terminal => "CT10.terminal.ct15"
end NodeId
inductive Terminal where
  | scope
  | c5
  | ct3
  | ct7
  | ct15
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .c5 => .c5Terminal | .ct3 => .ct3Terminal
  | .ct7 => .ct7Terminal | .ct15 => .ct15Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) : Edge F input .scopeDecision .labelCertification
  | labelsCertified (state : LabelState F input) :
      Edge F input .labelCertification .classificationDecision
  | classificationClose {labels : LabelState F input}
      (certificate : C5Certificate F input labels) :
      Edge F input .classificationDecision .c5Terminal
  | classificationDirect {labels : LabelState F input}
      (state : DirectState F input labels) :
      Edge F input .classificationDecision .directDecision
  | classificationMissing {labels : LabelState F input}
      (state : MissingState F input labels) :
      Edge F input .classificationDecision .promotionCertification
  | directToCT3 {labels : LabelState F input} {direct : DirectState F input labels}
      (payload : DirectCT3Payload F input direct) : Edge F input .directDecision .ct3Terminal
  | directToCT7 {labels : LabelState F input} {direct : DirectState F input labels}
      (payload : CT7Payload F input direct) : Edge F input .directDecision .ct7Terminal
  | promotionCertified {labels : LabelState F input}
      {missing : MissingState F input labels}
      (state : PromotedState F input missing) :
      Edge F input .promotionCertification .promotedRoutingDecision
  | promotedToCT3 {labels : LabelState F input}
      {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : PromotedCT3Payload F input promoted) :
      Edge F input .promotedRoutingDecision .ct3Terminal
  | promotedToCT15 {labels : LabelState F input}
      {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : CT15Payload F input promoted) :
      Edge F input .promotedRoutingDecision .ct15Terminal
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
end StructuralExhaustion.CT10.Graph
