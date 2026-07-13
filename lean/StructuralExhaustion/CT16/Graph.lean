import StructuralExhaustion.CT16.Types

namespace StructuralExhaustion.CT16.Graph

inductive NodeId where
  | entry | supportScan | codeComputation | codeComparison
  | properTerminal | equalTerminal | mismatchTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT16.entry"
  | .supportScan => "CT16.search.support"
  | .codeComputation => "CT16.compute.closed-code"
  | .codeComparison => "CT16.decide.closed-code"
  | .properTerminal => "CT16.terminal.residual.proper-support"
  | .equalTerminal => "CT16.terminal.certificate.exact-code"
  | .mismatchTerminal => "CT16.terminal.residual.closed-type-mismatch"
end NodeId

inductive Terminal where | proper | equal | mismatch
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .proper => .properTerminal | .equal => .equalTerminal
  | .mismatch => .mismatchTerminal
end Terminal

inductive Edge {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | begin : Edge C ctx .entry .supportScan
  | proper (r : ProperSupportResidual C ctx) :
      Edge C ctx .supportScan .properTerminal
  | whole (s : WholeSupportState C ctx) :
      Edge C ctx .supportScan .codeComputation
  | codeReady (s : ClosedCodeState C ctx) :
      Edge C ctx .codeComputation .codeComparison
  | equal (c : ExactCodeCertificate C ctx) :
      Edge C ctx .codeComparison .equalTerminal
  | mismatch (r : ClosedTypeMismatchResidual C ctx) :
      Edge C ctx .codeComparison .mismatchTerminal

namespace Edge
def source {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b} (_ : Edge C ctx a b) := a
end Edge

inductive Path {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | nil (n) : Path C ctx n n
  | cons {a b z} : Edge C ctx a b → Path C ctx b z → Path C ctx a z
namespace Path
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b} : Path C ctx a b → List NodeId
  | .nil n => [n] | .cons e rest => e.source :: rest.trace
end Path
def ValidTrace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (xs : List NodeId) : Prop :=
  ∃ t : Terminal, ∃ p : Path C ctx .entry t.nodeId, p.trace = xs

end StructuralExhaustion.CT16.Graph
