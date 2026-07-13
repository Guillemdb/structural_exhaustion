import StructuralExhaustion.CT15.Search

namespace StructuralExhaustion.CT15.Graph

open StructuralExhaustion

universe uAmbient uBranch uCoordinate

inductive NodeId where
  | entry
  | rankComputation
  | rankSplit
  | ledgerComputation
  | ledgerComparison
  | rankDropTerminal
  | c4Terminal
  | fullRankLedgerTerminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT15.entry"
  | .rankComputation => "CT15.compute.targetRelativeRank"
  | .rankSplit => "CT15.search.firstRankDrop"
  | .ledgerComputation => "CT15.compute.fullRankLedger"
  | .ledgerComparison => "CT15.decide.ledgerCapacity"
  | .rankDropTerminal => "CT15.terminal.rankDrop"
  | .c4Terminal => "CT15.terminal.c4"
  | .fullRankLedgerTerminal => "CT15.terminal.fullRankLedger"

end NodeId

inductive Terminal where
  | rankDrop
  | c4
  | fullRankLedger
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .rankDrop => .rankDropTerminal
  | .c4 => .c4Terminal
  | .fullRankLedger => .fullRankLedgerTerminal

end Terminal

/-- Every edge consumes the exact predecessor state and emits the exact next
state, certificate, or residual. -/
inductive Edge {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT15.Spec.{uAmbient, uBranch, uCoordinate} P)
    (capability : CT15.Capability S) (input : CT15.Input P) :
    NodeId → NodeId → Type _ where
  | beginRank : Edge S capability input .entry .rankComputation
  | rankComputed (rank : CT15.RankState S capability input) :
      Edge S capability input .rankComputation .rankSplit
  | rankDropped {rank : CT15.RankState S capability input}
      (residual : CT15.RankDropResidual S capability input rank) :
      Edge S capability input .rankSplit .rankDropTerminal
  | rankFull {rank : CT15.RankState S capability input}
      (full : CT15.FullRankState S capability input rank) :
      Edge S capability input .rankSplit .ledgerComputation
  | ledgerComputed {rank : CT15.RankState S capability input}
      {full : CT15.FullRankState S capability input rank}
      (ledger : CT15.LedgerState S capability input full) :
      Edge S capability input .ledgerComputation .ledgerComparison
  | capacityExceeded {rank : CT15.RankState S capability input}
      {full : CT15.FullRankState S capability input rank}
      {ledger : CT15.LedgerState S capability input full}
      (certificate : CT15.C4Certificate S capability input ledger) :
      Edge S capability input .ledgerComparison .c4Terminal
  | capacityAvailable {rank : CT15.RankState S capability input}
      {full : CT15.FullRankState S capability input rank}
      {ledger : CT15.LedgerState S capability input full}
      (residual : CT15.FullRankLedgerResidual S capability input ledger) :
      Edge S capability input .ledgerComparison .fullRankLedgerTerminal

namespace Edge

def source {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT15.Spec.{uAmbient, uBranch, uCoordinate} P}
    {capability : CT15.Capability S} {input : CT15.Input P}
    {first second : NodeId}
    (_edge : Edge S capability input first second) : NodeId :=
  first

end Edge

inductive Path {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT15.Spec.{uAmbient, uBranch, uCoordinate} P)
    (capability : CT15.Capability S) (input : CT15.Input P) :
    NodeId → NodeId → Type _ where
  | nil (node : NodeId) : Path S capability input node node
  | cons {first second last : NodeId} :
      Edge S capability input first second →
      Path S capability input second last →
      Path S capability input first last

namespace Path

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT15.Spec.{uAmbient, uBranch, uCoordinate} P}
    {capability : CT15.Capability S} {input : CT15.Input P}
    {first last : NodeId} :
    Path S capability input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT15.Spec.{uAmbient, uBranch, uCoordinate} P}
    {capability : CT15.Capability S} {input : CT15.Input P}
    (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path S capability input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT15.Graph
