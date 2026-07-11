import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | localityCertification
  | deficitDecision
  | ct11Terminal
  | summationCertification
  | comparisonDecision
  | c4Terminal
  | ct4Terminal
  | ct14Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT5.entry"
  | .scopeDecision => "CT5.decide.scope"
  | .scopeTerminal => "CT5.terminal.scope"
  | .localityCertification => "CT5.certify.locality"
  | .deficitDecision => "CT5.decide.deficit"
  | .ct11Terminal => "CT5.terminal.ct11"
  | .summationCertification => "CT5.certify.summation"
  | .comparisonDecision => "CT5.decide.comparison"
  | .c4Terminal => "CT5.terminal.c4"
  | .ct4Terminal => "CT5.terminal.ct4"
  | .ct14Terminal => "CT5.terminal.ct14"

end NodeId

inductive Terminal where
  | scope
  | ct11
  | c4
  | ct4
  | ct14
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .ct11 => .ct11Terminal
  | .c4 => .c4Terminal
  | .ct4 => .ct4Terminal
  | .ct14 => .ct14Terminal

end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .localityCertification
  | localityCertified (state : LocalityState F input) :
      Edge F input .localityCertification .deficitDecision
  | deficitToCT11 {locality : LocalityState F input}
      (payload : CT11Payload F input locality) :
      Edge F input .deficitDecision .ct11Terminal
  | deficitLedger {locality : LocalityState F input}
      (state : LocalLedgerState F input locality) :
      Edge F input .deficitDecision .summationCertification
  | summationCertified {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      (state : SummationState F input ledger) :
      Edge F input .summationCertification .comparisonDecision
  | comparisonClose {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (certificate : C4Certificate F input summation) :
      Edge F input .comparisonDecision .c4Terminal
  | comparisonToCT4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT4Payload F input summation) :
      Edge F input .comparisonDecision .ct4Terminal
  | comparisonToCT14 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT14Payload F input summation) :
      Edge F input .comparisonDecision .ct14Terminal

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
    ∃ path : Path F input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT5.Graph
