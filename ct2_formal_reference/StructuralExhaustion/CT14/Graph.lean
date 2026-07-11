import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Graph
inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | boundsCertification
  | multiplicityDecision
  | ct9Terminal
  | ct10Terminal
  | comparisonCertification
  | c4Terminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT14.entry" | .scopeDecision => "CT14.decide.scope"
  | .scopeTerminal => "CT14.terminal.scope"
  | .boundsCertification => "CT14.certify.bounds"
  | .multiplicityDecision => "CT14.decide.multiplicity"
  | .ct9Terminal => "CT14.terminal.ct9" | .ct10Terminal => "CT14.terminal.ct10"
  | .comparisonCertification => "CT14.certify.comparison"
  | .c4Terminal => "CT14.terminal.c4"
end NodeId
inductive Terminal where
  | scope
  | ct9
  | ct10
  | c4
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .ct9 => .ct9Terminal
  | .ct10 => .ct10Terminal | .c4 => .c4Terminal
end Terminal
inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) : Edge F input .scopeDecision .boundsCertification
  | boundsCertified (state : BoundsState F input) :
      Edge F input .boundsCertification .multiplicityDecision
  | multiplicityUnbounded {bounds : BoundsState F input} (payload : CT9Payload F input bounds) :
      Edge F input .multiplicityDecision .ct9Terminal
  | multiplicityMissing {bounds : BoundsState F input} (payload : CT10Payload F input bounds) :
      Edge F input .multiplicityDecision .ct10Terminal
  | multiplicityCounted {bounds : BoundsState F input}
      (state : MultiplicityState F input bounds) :
      Edge F input .multiplicityDecision .comparisonCertification
  | comparisonClose {bounds : BoundsState F input}
      {multiplicity : MultiplicityState F input bounds}
      (certificate : C4Certificate F input multiplicity) :
      Edge F input .comparisonCertification .c4Terminal
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
end StructuralExhaustion.CT14.Graph
