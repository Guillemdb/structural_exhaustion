import StructuralExhaustion.CT5.Search

namespace StructuralExhaustion.CT5.Graph

inductive NodeId where
  | entry | deficitSearch | summation | comparison
  | deficitTerminal | c4Terminal | chargeTerminal | aggregateTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT5.entry"
  | .deficitSearch => "CT5.search.deficit"
  | .summation => "CT5.compute.summation"
  | .comparison => "CT5.decide.comparison"
  | .deficitTerminal => "CT5.terminal.residual.localDeficit"
  | .c4Terminal => "CT5.terminal.c4"
  | .chargeTerminal => "CT5.terminal.residual.chargeLedger"
  | .aggregateTerminal => "CT5.terminal.residual.aggregate"
end NodeId

inductive Terminal where
  | deficit | c4 | charge | aggregate
  deriving Repr, DecidableEq

namespace Terminal
def nodeId : Terminal → NodeId
  | .deficit => .deficitTerminal
  | .c4 => .c4Terminal
  | .charge => .chargeTerminal
  | .aggregate => .aggregateTerminal
end Terminal

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

inductive Edge : NodeId → NodeId → Type _ where
  | beginDeficit : Edge .entry .deficitSearch
  | deficitFound (residual : LocalDeficitResidual S input) :
      Edge .deficitSearch .deficitTerminal
  | deficitAbsent (state : DeficitFreeState S capability input) :
      Edge .deficitSearch .summation
  | summed (ledger : LocalLedgerState S capability input) :
      Edge .summation .comparison
  | comparisonC4 (certificate : C4Certificate S capability input) :
      Edge .comparison .c4Terminal
  | comparisonCharge (residual : ChargeLedgerResidual S capability input) :
      Edge .comparison .chargeTerminal
  | comparisonAggregate (residual : AggregateResidual S capability input) :
      Edge .comparison .aggregateTerminal

namespace Edge
def source {first second} (_ : Edge S capability input first second) := first
end Edge

inductive Path : NodeId → NodeId → Type _ where
  | nil (node) : Path node node
  | cons {first second last} : Edge S capability input first second →
      Path second last → Path first last

namespace Path
def trace {first last} : Path S capability input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path

def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path S capability input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT5.Graph
