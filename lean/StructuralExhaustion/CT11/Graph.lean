import StructuralExhaustion.CT11.Search

namespace StructuralExhaustion.CT11.Graph

universe uAmbient uBranch uCell

inductive NodeId where
  | entry | decomposition | admissibility | localization
  | gapTerminal | localizedTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT11.entry"
  | .decomposition => "CT11.compute.decomposition"
  | .admissibility => "CT11.search.admissibilityGap"
  | .localization => "CT11.search.localNegativeBudget"
  | .gapTerminal => "CT11.terminal.residual.admissibilityGap"
  | .localizedTerminal => "CT11.terminal.residual.localizedDeficit"
end NodeId

inductive Terminal where | gap | localized deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .gap => .gapTerminal
  | .localized => .localizedTerminal
end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uCell} P)
variable (input : Input capability)

inductive Edge : NodeId → NodeId → Type _ where
  | begin : Edge .entry .decomposition
  | decomposed : Edge .decomposition .admissibility
  | gap (r : AdmissibilityGapResidual capability input) : Edge .admissibility .gapTerminal
  | closed (s : AdmissibleDecomposition capability input) : Edge .admissibility .localization
  | localized (r : LocalizedDeficitResidual capability input) :
      Edge .localization .localizedTerminal

namespace Edge
def source {a b} (_ : Edge capability input a b) := a
end Edge

inductive Path : NodeId → NodeId → Type _ where
  | nil (n) : Path n n
  | cons {a b c} : Edge capability input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path capability input a b → List NodeId
  | .nil n => [n]
  | .cons e p => e.source :: p.trace
end Path

def ValidTrace (nodes : List NodeId) : Prop := ∃ terminal : Terminal,
  ∃ path : Path capability input .entry terminal.nodeId, path.trace = nodes

end StructuralExhaustion.CT11.Graph
