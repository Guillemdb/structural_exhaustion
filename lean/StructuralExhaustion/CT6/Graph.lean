import StructuralExhaustion.CT6.Search

namespace StructuralExhaustion.CT6.Graph

inductive NodeId where
  | entry | firstFailureSearch | firstFailureTerminal | activeLedgerTerminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT6.entry"
  | .firstFailureSearch => "CT6.search.firstFailure"
  | .firstFailureTerminal => "CT6.terminal.residual.firstFailure"
  | .activeLedgerTerminal => "CT6.terminal.residual.activeLedger"
end NodeId
inductive Terminal where | firstFailure | activeLedger
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .firstFailure => .firstFailureTerminal
  | .activeLedger => .activeLedgerTerminal
end Terminal

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)
inductive Edge : NodeId → NodeId → Type _ where
  | beginSearch : Edge .entry .firstFailureSearch
  | failure (residual : FirstFailureResidual S capability input) :
      Edge .firstFailureSearch .firstFailureTerminal
  | active (residual : ActiveLedgerResidual S capability input) :
      Edge .firstFailureSearch .activeLedgerTerminal
namespace Edge
def source {a b} (_ : Edge S capability input a b) := a
end Edge
inductive Path : NodeId → NodeId → Type _ where
  | nil (node) : Path node node
  | cons {a b c} : Edge S capability input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path S capability input a b → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path
def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path S capability input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT6.Graph
