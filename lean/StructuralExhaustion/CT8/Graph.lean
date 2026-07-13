import StructuralExhaustion.CT8.Search

namespace StructuralExhaustion.CT8.Graph

universe uAmbient uBranch uState uType uResponseContext

inductive NodeId where
  | entry | repetition | response
  | noRepetitionTerminal | removalTerminal | separationTerminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT8.entry"
  | .repetition => "CT8.search.orderedRepeatedType"
  | .response => "CT8.compare.responses"
  | .noRepetitionTerminal => "CT8.terminal.certificate.noRepetition"
  | .removalTerminal => "CT8.terminal.residual.removal"
  | .separationTerminal => "CT8.terminal.residual.responseSeparation"
end NodeId

inductive Terminal where | noRepetition | removal | separation deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .noRepetition => .noRepetitionTerminal
  | .removal => .removalTerminal
  | .separation => .separationTerminal
end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)
variable (ctx : Core.BranchContext P)
variable (input : Input capability ctx)

inductive Edge : NodeId → NodeId → Type _ where
  | begin : Edge .entry .repetition
  | unique (c : NoRepetitionCertificate capability ctx input) :
      Edge .repetition .noRepetitionTerminal
  | repeated (p : OrderedRepeatedPair capability input.sequence) :
      Edge .repetition .response
  | removable (r : RemovalResidual capability ctx input) : Edge .response .removalTerminal
  | separating (r : SeparationResidual capability ctx input) :
      Edge .response .separationTerminal
namespace Edge
def source {a b} (_ : Edge capability ctx input a b) := a
end Edge
inductive Path : NodeId → NodeId → Type _ where
  | nil (n) : Path n n
  | cons {a b c} : Edge capability ctx input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path capability ctx input a b → List NodeId
  | .nil n => [n]
  | .cons e p => e.source :: p.trace
end Path
def ValidTrace (nodes : List NodeId) : Prop := ∃ terminal : Terminal,
  ∃ path : Path capability ctx input .entry terminal.nodeId, path.trace = nodes

end StructuralExhaustion.CT8.Graph
