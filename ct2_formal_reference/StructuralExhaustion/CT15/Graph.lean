import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Graph
inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | rankCertification
  | rankDropDecision
  | dependenceRoutingDecision
  | ct3Terminal
  | ct7Terminal
  | ct16Terminal
  | ledgerCertification
  | comparisonDecision
  | c4Terminal
  | ct4Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT15.entry" | .scopeDecision => "CT15.decide.scope"
  | .scopeTerminal => "CT15.terminal.scope" | .rankCertification => "CT15.certify.rank"
  | .rankDropDecision => "CT15.decide.rankDrop"
  | .dependenceRoutingDecision => "CT15.decide.dependenceRouting"
  | .ct3Terminal => "CT15.terminal.ct3" | .ct7Terminal => "CT15.terminal.ct7"
  | .ct16Terminal => "CT15.terminal.ct16" | .ledgerCertification => "CT15.certify.ledger"
  | .comparisonDecision => "CT15.decide.comparison" | .c4Terminal => "CT15.terminal.c4"
  | .ct4Terminal => "CT15.terminal.ct4"
end NodeId
inductive Terminal where
  | scope
  | ct3
  | ct7
  | ct16
  | c4
  | ct4
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct3 => .ct3Terminal | .ct7 => .ct7Terminal
  | .ct16 => .ct16Terminal | .c4 => .c4Terminal | .ct4 => .ct4Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeReady (scope : ScopedState F input) : Edge F input .scopeDecision .rankCertification
  | rankCertified (rank : RankState F input) : Edge F input .rankCertification .rankDropDecision
  | rankDependent {rank : RankState F input} (dependence : DependenceState F input rank) :
      Edge F input .rankDropDecision .dependenceRoutingDecision
  | rankFull {rank : RankState F input} (full : FullRankState F input rank) :
      Edge F input .rankDropDecision .ledgerCertification
  | dependenceToCT3 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT3Payload F input dependence) :
      Edge F input .dependenceRoutingDecision .ct3Terminal
  | dependenceToCT7 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT7Payload F input dependence) :
      Edge F input .dependenceRoutingDecision .ct7Terminal
  | dependenceToCT16 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT16Payload F input dependence) :
      Edge F input .dependenceRoutingDecision .ct16Terminal
  | ledgerCertified {rank : RankState F input} {full : FullRankState F input rank}
      (ledger : LedgerState F input full) : Edge F input .ledgerCertification .comparisonDecision
  | comparisonClose {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (certificate : C4Certificate F input ledger) :
      Edge F input .comparisonDecision .c4Terminal
  | comparisonToCT4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (payload : CT4Payload F input ledger) :
      Edge F input .comparisonDecision .ct4Terminal
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
end StructuralExhaustion.CT15.Graph
