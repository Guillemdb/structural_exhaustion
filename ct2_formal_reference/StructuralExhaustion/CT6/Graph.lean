import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | definitionCertification
  | activityDecision
  | activeLedgerCertification
  | ct4Terminal
  | dormantDecision
  | c1Terminal
  | ct3Terminal
  | ct7Terminal
  | ct9Terminal
  | ct10Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT6.entry"
  | .scopeDecision => "CT6.decide.scope"
  | .scopeTerminal => "CT6.terminal.scope"
  | .definitionCertification => "CT6.certify.definition"
  | .activityDecision => "CT6.decide.activity"
  | .activeLedgerCertification => "CT6.certify.activeLedger"
  | .ct4Terminal => "CT6.terminal.ct4"
  | .dormantDecision => "CT6.decide.dormant"
  | .c1Terminal => "CT6.terminal.c1"
  | .ct3Terminal => "CT6.terminal.ct3"
  | .ct7Terminal => "CT6.terminal.ct7"
  | .ct9Terminal => "CT6.terminal.ct9"
  | .ct10Terminal => "CT6.terminal.ct10"

end NodeId

inductive Terminal where
  | scope
  | ct4
  | c1
  | ct3
  | ct7
  | ct9
  | ct10
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .ct4 => .ct4Terminal
  | .c1 => .c1Terminal
  | .ct3 => .ct3Terminal
  | .ct7 => .ct7Terminal
  | .ct9 => .ct9Terminal
  | .ct10 => .ct10Terminal

end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .definitionCertification
  | definitionCertified (state : DefinitionState F input) :
      Edge F input .definitionCertification .activityDecision
  | activityActive {definition : DefinitionState F input}
      (state : ActiveState F input definition) :
      Edge F input .activityDecision .activeLedgerCertification
  | activityDormant {definition : DefinitionState F input}
      (state : DormantState F input definition) :
      Edge F input .activityDecision .dormantDecision
  | activeLedgerToCT4 {definition : DefinitionState F input}
      {active : ActiveState F input definition}
      (payload : CT4Payload F input active) :
      Edge F input .activeLedgerCertification .ct4Terminal
  | dormantClose {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (certificate : C1Certificate F input dormant) :
      Edge F input .dormantDecision .c1Terminal
  | dormantToCT3 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT3Payload F input dormant) :
      Edge F input .dormantDecision .ct3Terminal
  | dormantToCT7 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT7Payload F input dormant) :
      Edge F input .dormantDecision .ct7Terminal
  | dormantToCT9 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT9Payload F input dormant) :
      Edge F input .dormantDecision .ct9Terminal
  | dormantToCT10 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT10Payload F input dormant) :
      Edge F input .dormantDecision .ct10Terminal

namespace Edge

def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src

end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} :
      Edge F input first second → Path F input second last →
      Path F input first last

namespace Path

def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path F input .entry terminal.nodeId, path.trace = nodes

end StructuralExhaustion.CT6.Graph
