import StructuralExhaustion.CT13.Types

namespace StructuralExhaustion.CT13.Graph

inductive NodeId where
  | entry | tierOne | fallback | reconciliation | comparison
  | tierOneTerminal | overlapTerminal | deficitTerminal | reconciledTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT13.entry"
  | .tierOne => "CT13.search.tier-one"
  | .fallback => "CT13.compute.fallback"
  | .reconciliation => "CT13.compute.reconciliation"
  | .comparison => "CT13.decide.comparison"
  | .tierOneTerminal => "CT13.terminal.residual.tier-one"
  | .overlapTerminal => "CT13.terminal.residual.overlap"
  | .deficitTerminal => "CT13.terminal.residual.deficit"
  | .reconciledTerminal => "CT13.terminal.certificate.reconciled"
end NodeId

inductive Terminal where | tierOne | overlap | deficit | reconciled
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .tierOne => .tierOneTerminal | .overlap => .overlapTerminal
  | .deficit => .deficitTerminal | .reconciled => .reconciledTerminal
end Terminal

inductive Edge {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | begin : Edge C ctx .entry .tierOne
  | tierOne (r : TierOneResidual C ctx) : Edge C ctx .tierOne .tierOneTerminal
  | absent (s : TierOneAbsenceState C ctx) : Edge C ctx .tierOne .fallback
  | fallback (s : FallbackState C ctx) : Edge C ctx .fallback .reconciliation
  | overlap (r : OverlapResidual C ctx) : Edge C ctx .reconciliation .overlapTerminal
  | clean (s : ReconciledState C ctx) : Edge C ctx .reconciliation .comparison
  | deficit (r : DeficitResidual C ctx) : Edge C ctx .comparison .deficitTerminal
  | reconciled (c : ReconciliationCertificate C ctx) :
      Edge C ctx .comparison .reconciledTerminal

namespace Edge
def source {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b : NodeId} (_ : Edge C ctx a b) : NodeId := a
end Edge

inductive Path {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | nil (n : NodeId) : Path C ctx n n
  | cons {a b z : NodeId} : Edge C ctx a b → Path C ctx b z → Path C ctx a z
namespace Path
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b : NodeId} : Path C ctx a b → List NodeId
  | .nil n => [n]
  | .cons edge rest => edge.source :: rest.trace
end Path
def ValidTrace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (xs : List NodeId) : Prop :=
  ∃ t : Terminal, ∃ path : Path C ctx .entry t.nodeId, path.trace = xs

end StructuralExhaustion.CT13.Graph
