import StructuralExhaustion.CT12.State

namespace StructuralExhaustion.CT12.Graph

universe uAmbient uBranch uState uPeeled uDemand uTier

inductive NodeId where
  | entry | saturation | peel | restoration | decrease
  | exhaustedTerminal | demandTerminal | tierTerminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT12.entry"
  | .saturation => "CT12.decide.saturation"
  | .peel => "CT12.compute.peel"
  | .restoration => "CT12.compute.restoration"
  | .decrease => "CT12.verify.decrease"
  | .exhaustedTerminal => "CT12.terminal.certificate.exhausted"
  | .demandTerminal => "CT12.terminal.residual.demand"
  | .tierTerminal => "CT12.terminal.residual.tier"
end NodeId

inductive Terminal where | exhausted | demand | tier deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .exhausted => .exhaustedTerminal
  | .demand => .demandTerminal
  | .tier => .tierTerminal
end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P)

inductive Edge : NodeId → NodeId → Type _ where
  | begin : Edge .entry .saturation
  | exhausted (state : capability.State 0) : Edge .saturation .exhaustedTerminal
  | positive {n : Nat} (state : capability.State (n + 1)) : Edge .saturation .peel
  | peeled {n : Nat} {state : capability.State (n + 1)}
      (peeled : capability.Peeled state) : Edge .peel .restoration
  | demand {n : Nat} {state : capability.State (n + 1)}
      (peeled : capability.Peeled state) (residual : capability.DemandResidual) :
      Edge .restoration .demandTerminal
  | tier {n : Nat} {state : capability.State (n + 1)}
      (peeled : capability.Peeled state) (residual : capability.TierResidual) :
      Edge .restoration .tierTerminal
  | continue {n next : Nat} {state : capability.State (n + 1)}
      (peeled : capability.Peeled state) (nextState : capability.State next)
      (decreases : next < n + 1) : Edge .restoration .decrease
  | loopBack {n next : Nat} {state : capability.State (n + 1)}
      (peeled : capability.Peeled state) (nextState : capability.State next)
      (decreases : next < n + 1) : Edge .decrease .saturation

namespace Edge
def source {a b} (_ : Edge capability a b) := a
end Edge
inductive Path : NodeId → NodeId → Type _ where
  | nil (n) : Path n n
  | cons {a b c} : Edge capability a b → Path b c → Path a c
namespace Path
def trace {a b} : Path capability a b → List NodeId
  | .nil n => [n]
  | .cons e p => e.source :: p.trace
end Path

def ValidTrace (nodes : List NodeId) : Prop := ∃ terminal : Terminal,
  ∃ path : Path capability .entry terminal.nodeId, path.trace = nodes

end StructuralExhaustion.CT12.Graph
