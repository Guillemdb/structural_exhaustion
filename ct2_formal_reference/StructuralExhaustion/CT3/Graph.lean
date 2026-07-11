import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | equivalenceCertification
  | compressionDecision
  | c2Terminal
  | defectDecision
  | c3Terminal
  | ct7Terminal
  | ct12Terminal
  | tableDecision
  | c5Terminal
  | ct8Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT3.entry"
  | .scopeDecision => "CT3.decide.scope"
  | .scopeTerminal => "CT3.terminal.scope"
  | .equivalenceCertification => "CT3.certify.equivalence"
  | .compressionDecision => "CT3.decide.compression"
  | .c2Terminal => "CT3.terminal.c2"
  | .defectDecision => "CT3.decide.defect"
  | .c3Terminal => "CT3.terminal.c3"
  | .ct7Terminal => "CT3.terminal.ct7"
  | .ct12Terminal => "CT3.terminal.ct12"
  | .tableDecision => "CT3.decide.table"
  | .c5Terminal => "CT3.terminal.c5"
  | .ct8Terminal => "CT3.terminal.ct8"

end NodeId

inductive Terminal where
  | scope
  | c2
  | c3
  | ct7
  | ct12
  | c5
  | ct8
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .c2 => .c2Terminal
  | .c3 => .c3Terminal
  | .ct7 => .ct7Terminal
  | .ct12 => .ct12Terminal
  | .c5 => .c5Terminal
  | .ct8 => .ct8Terminal

end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .equivalenceCertification
  | equivalenceCertified (state : EquivalenceState F input) :
      Edge F input .equivalenceCertification .compressionDecision
  | compressionClose {equivalence : EquivalenceState F input}
      (certificate : C2Certificate F input equivalence) :
      Edge F input .compressionDecision .c2Terminal
  | compressionResidual {equivalence : EquivalenceState F input}
      (state : UncompressibleState F input equivalence) :
      Edge F input .compressionDecision .defectDecision
  | defectClose {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (certificate : C3Certificate F input state) :
      Edge F input .defectDecision .c3Terminal
  | defectToCT7 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT7Payload F input state) :
      Edge F input .defectDecision .ct7Terminal
  | defectToCT12 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT12Payload F input state) :
      Edge F input .defectDecision .ct12Terminal
  | defectPersistent {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (persistent : PersistentState F input state) :
      Edge F input .defectDecision .tableDecision
  | tableClose {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (certificate : C5Certificate F input persistent) :
      Edge F input .tableDecision .c5Terminal
  | tableToCT8 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (payload : CT8Payload F input persistent) :
      Edge F input .tableDecision .ct8Terminal

namespace Edge

def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src

def target {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := dst

end Edge

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

def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path F input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT3.Graph
