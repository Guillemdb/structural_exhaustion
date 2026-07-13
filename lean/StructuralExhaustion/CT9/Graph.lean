import StructuralExhaustion.CT9.Search

namespace StructuralExhaustion.CT9.Graph

universe uAmbient uBranch uItem uLabel

inductive NodeId where
  | entry | partition | overload
  | overloadedTerminal | boundedTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT9.entry"
  | .partition => "CT9.compute.partition"
  | .overload => "CT9.search.firstOverload"
  | .overloadedTerminal => "CT9.terminal.residual.overload"
  | .boundedTerminal => "CT9.terminal.certificate.bounded"
end NodeId

inductive Terminal where | overloaded | bounded deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .overloaded => .overloadedTerminal
  | .bounded => .boundedTerminal
end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
variable (input : Input capability)

inductive Edge : NodeId → NodeId → Type _ where
  | begin : Edge .entry .partition
  | partitioned : Edge .partition .overload
  | overloaded (residual : OverloadResidual capability input) :
      Edge .overload .overloadedTerminal
  | bounded (certificate : BoundedCertificate capability input) :
      Edge .overload .boundedTerminal

namespace Edge
def source {a b} (_ : Edge capability input a b) := a
end Edge

inductive Path : NodeId → NodeId → Type _ where
  | nil (node) : Path node node
  | cons {a b c} : Edge capability input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path capability input a b → List NodeId
  | .nil n => [n]
  | .cons e rest => e.source :: rest.trace
end Path

def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path capability input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT9.Graph
