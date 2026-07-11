import StructuralExhaustion.CT7.Types

namespace StructuralExhaustion.CT7.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | contextCertification
  | realizationDecision
  | c1Terminal
  | distinctionDecision
  | defectDecision
  | c3Terminal
  | ct3Terminal
  | ct12Terminal
  | neutralDecision
  | c2Terminal
  | ct10Terminal
  | ct16Terminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT7.entry"
  | .scopeDecision => "CT7.decide.scope"
  | .scopeTerminal => "CT7.terminal.scope"
  | .contextCertification => "CT7.certify.context"
  | .realizationDecision => "CT7.decide.realization"
  | .c1Terminal => "CT7.terminal.c1"
  | .distinctionDecision => "CT7.decide.distinction"
  | .defectDecision => "CT7.decide.defect"
  | .c3Terminal => "CT7.terminal.c3"
  | .ct3Terminal => "CT7.terminal.ct3"
  | .ct12Terminal => "CT7.terminal.ct12"
  | .neutralDecision => "CT7.decide.neutral"
  | .c2Terminal => "CT7.terminal.c2"
  | .ct10Terminal => "CT7.terminal.ct10"
  | .ct16Terminal => "CT7.terminal.ct16"
end NodeId

inductive Terminal where
  | scope
  | c1
  | c3
  | ct3
  | ct12
  | c2
  | ct10
  | ct16
  deriving Repr, DecidableEq

namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .c1 => .c1Terminal
  | .c3 => .c3Terminal
  | .ct3 => .ct3Terminal
  | .ct12 => .ct12Terminal
  | .c2 => .c2Terminal
  | .ct10 => .ct10Terminal
  | .ct16 => .ct16Terminal
end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .contextCertification
  | contextCertified (state : ContextState F input) :
      Edge F input .contextCertification .realizationDecision
  | realizationClose {context : ContextState F input}
      (certificate : C1Certificate F input context) :
      Edge F input .realizationDecision .c1Terminal
  | realizationUnrealized {context : ContextState F input}
      (state : UnrealizedState F input context) :
      Edge F input .realizationDecision .distinctionDecision
  | distinctionDefect {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      (state : DefectState F input unrealized) :
      Edge F input .distinctionDecision .defectDecision
  | distinctionNeutral {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      (state : NeutralState F input unrealized) :
      Edge F input .distinctionDecision .neutralDecision
  | defectClose {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (certificate : C3Certificate F input defect) :
      Edge F input .defectDecision .c3Terminal
  | defectToCT3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT3Payload F input defect) :
      Edge F input .defectDecision .ct3Terminal
  | defectToCT12 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT12Payload F input defect) :
      Edge F input .defectDecision .ct12Terminal
  | neutralClose {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (certificate : C2Certificate F input neutral) :
      Edge F input .neutralDecision .c2Terminal
  | neutralToCT10 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT10Payload F input neutral) :
      Edge F input .neutralDecision .ct10Terminal
  | neutralToCT16 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT16Payload F input neutral) :
      Edge F input .neutralDecision .ct16Terminal

namespace Edge
def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src
end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} :
      Edge F input first second → Path F input second last → Path F input first last

namespace Path
def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path

def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path F input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT7.Graph
