import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Graph
inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | ct10Terminal
  | fibreCertification
  | overloadDecision
  | ct4Terminal
  | extractionCertification
  | routingDecision
  | c1Terminal
  | ct7Terminal
  | ct8Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT9.entry"
  | .scopeDecision => "CT9.decide.scope"
  | .scopeTerminal => "CT9.terminal.scope"
  | .ct10Terminal => "CT9.terminal.ct10"
  | .fibreCertification => "CT9.certify.fibre"
  | .overloadDecision => "CT9.decide.overload"
  | .ct4Terminal => "CT9.terminal.ct4"
  | .extractionCertification => "CT9.certify.extraction"
  | .routingDecision => "CT9.decide.routing"
  | .c1Terminal => "CT9.terminal.c1"
  | .ct7Terminal => "CT9.terminal.ct7"
  | .ct8Terminal => "CT9.terminal.ct8"
end NodeId
inductive Terminal where
  | scope
  | ct10
  | ct4
  | c1
  | ct7
  | ct8
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct10 => .ct10Terminal | .ct4 => .ct4Terminal
  | .c1 => .c1Terminal | .ct7 => .ct7Terminal | .ct8 => .ct8Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeRefine (payload : CT10Payload F input) : Edge F input .scopeDecision .ct10Terminal
  | scopeReady (state : ScopedState F input) : Edge F input .scopeDecision .fibreCertification
  | fibreCertified (state : FibreState F input) :
      Edge F input .fibreCertification .overloadDecision
  | overloadBounded {fibre : FibreState F input} (payload : CT4Payload F input fibre) :
      Edge F input .overloadDecision .ct4Terminal
  | overloadPresent {fibre : FibreState F input}
      (state : OverloadedState F input fibre) :
      Edge F input .overloadDecision .extractionCertification
  | extractionCertified {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      (state : ExtractionState F input overloaded) :
      Edge F input .extractionCertification .routingDecision
  | routingClose {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (certificate : C1Certificate F input extraction) :
      Edge F input .routingDecision .c1Terminal
  | routingToCT7 {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT7Payload F input extraction) : Edge F input .routingDecision .ct7Terminal
  | routingToCT8 {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT8Payload F input extraction) : Edge F input .routingDecision .ct8Terminal
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
end StructuralExhaustion.CT9.Graph
