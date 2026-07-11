import StructuralExhaustion.CT13.Types

namespace StructuralExhaustion.CT13.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | availabilityDecision
  | tierOneCertification
  | tierOneRoutingCertification
  | ct4Terminal
  | fallbackCertification
  | reconciliationDecision
  | comparisonCertification
  | c4Terminal
  | overlapRoutingDecision
  | ct9Terminal
  | ct14Terminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT13.entry"
  | .scopeDecision => "CT13.decide.scope"
  | .scopeTerminal => "CT13.terminal.scope"
  | .availabilityDecision => "CT13.decide.availability"
  | .tierOneCertification => "CT13.certify.tierOne"
  | .tierOneRoutingCertification => "CT13.certify.tierOneRouting"
  | .ct4Terminal => "CT13.terminal.ct4"
  | .fallbackCertification => "CT13.certify.fallback"
  | .reconciliationDecision => "CT13.decide.reconciliation"
  | .comparisonCertification => "CT13.certify.comparison"
  | .c4Terminal => "CT13.terminal.c4"
  | .overlapRoutingDecision => "CT13.decide.overlapRouting"
  | .ct9Terminal => "CT13.terminal.ct9"
  | .ct14Terminal => "CT13.terminal.ct14"
end NodeId

inductive Terminal where
  | scope
  | ct4
  | c4
  | ct9
  | ct14
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct4 => .ct4Terminal | .c4 => .c4Terminal
  | .ct9 => .ct9Terminal | .ct14 => .ct14Terminal
end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (scope : ScopedState F input) :
      Edge F input .scopeDecision .availabilityDecision
  | availabilityYes {scope : ScopedState F input}
      (available : AvailableState F input scope) :
      Edge F input .availabilityDecision .tierOneCertification
  | availabilityNo {scope : ScopedState F input}
      (unavailable : UnavailableState F input scope) :
      Edge F input .availabilityDecision .fallbackCertification
  | tierOneCertified {scope : ScopedState F input}
      {available : AvailableState F input scope}
      (tierOne : TierOneState F input available) :
      Edge F input .tierOneCertification .tierOneRoutingCertification
  | tierOneToCT4 {scope : ScopedState F input}
      {available : AvailableState F input scope}
      {tierOne : TierOneState F input available}
      (payload : CT4Payload F input tierOne) :
      Edge F input .tierOneRoutingCertification .ct4Terminal
  | fallbackCertified {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      (fallback : FallbackState F input unavailable) :
      Edge F input .fallbackCertification .reconciliationDecision
  | reconciliationYes {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      (reconciled : ReconciledState F input fallback) :
      Edge F input .reconciliationDecision .comparisonCertification
  | reconciliationOverlap {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      (overlap : OverlapState F input fallback) :
      Edge F input .reconciliationDecision .overlapRoutingDecision
  | comparisonClose {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {reconciled : ReconciledState F input fallback}
      (certificate : C4Certificate F input reconciled) :
      Edge F input .comparisonCertification .c4Terminal
  | overlapToCT9 {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback}
      (payload : CT9Payload F input overlap) :
      Edge F input .overlapRoutingDecision .ct9Terminal
  | overlapToCT14 {scope : ScopedState F input}
      {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback}
      (payload : CT14Payload F input overlap) :
      Edge F input .overlapRoutingDecision .ct14Terminal

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
  ∃ terminal : Terminal, ∃ path : Path F input .entry terminal.nodeId,
    path.trace = nodes
end StructuralExhaustion.CT13.Graph
