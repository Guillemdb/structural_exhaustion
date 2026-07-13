import StructuralExhaustion.CT7.Search

namespace StructuralExhaustion.CT7.Graph

inductive NodeId where
  | entry | realizationSearch | distinctionSearch
  | realizationTerminal | distinguishingTerminal | neutralTerminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT7.entry"
  | .realizationSearch => "CT7.search.realization"
  | .distinctionSearch => "CT7.search.distinction"
  | .realizationTerminal => "CT7.terminal.certificate.realization"
  | .distinguishingTerminal => "CT7.terminal.residual.distinguishing"
  | .neutralTerminal => "CT7.terminal.certificate.neutrality"
end NodeId
inductive Terminal where | realization | distinguishing | neutral
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .realization => .realizationTerminal
  | .distinguishing => .distinguishingTerminal
  | .neutral => .neutralTerminal
end Terminal

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (ctx : Core.BranchContext P) (input : Input S ctx)
inductive Edge : NodeId → NodeId → Type _ where
  | beginRealization : Edge .entry .realizationSearch
  | realized (certificate : RealizationCertificate S capability ctx input) :
      Edge .realizationSearch .realizationTerminal
  | unrealized (state : UnrealizedState S capability ctx input) :
      Edge .realizationSearch .distinctionSearch
  | distinguished (residual : DistinguishingResidual S capability ctx input) :
      Edge .distinctionSearch .distinguishingTerminal
  | neutral (certificate : NeutralityCertificate S capability ctx input) :
      Edge .distinctionSearch .neutralTerminal
namespace Edge
def source {a b} (_ : Edge S capability ctx input a b) := a
end Edge
inductive Path : NodeId → NodeId → Type _ where
  | nil (node) : Path node node
  | cons {a b c} : Edge S capability ctx input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path S capability ctx input a b → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path
def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path S capability ctx input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT7.Graph
