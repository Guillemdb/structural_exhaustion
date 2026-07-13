import StructuralExhaustion.CT16.Graph

namespace StructuralExhaustion.CT16

inductive RawOutcome {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Graph.Terminal → Type _ where
  | proper (r : ProperSupportResidual C ctx) : RawOutcome C ctx .proper
  | equal (c : ExactCodeCertificate C ctx) : RawOutcome C ctx .equal
  | mismatch (r : ClosedTypeMismatchResidual C ctx) : RawOutcome C ctx .mismatch

structure ExecutionResult {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  terminal : Graph.Terminal
  path : Graph.Path C ctx .entry terminal.nodeId
  outcome : RawOutcome C ctx terminal
namespace ExecutionResult
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (r : ExecutionResult C ctx) := r.path.trace
end ExecutionResult

def runReference {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (_input : Input C ctx) : ExecutionResult C ctx :=
  match scanSupport C ctx with
  | .proper residual => ⟨.proper,
      .cons .begin (.cons (.proper residual) (.nil .properTerminal)),
      .proper residual⟩
  | .whole whole =>
      let code := computeCode C ctx whole
      match compareCode C ctx code with
      | .equal certificate => ⟨.equal,
          .cons .begin (.cons (.whole whole)
            (.cons (.codeReady code)
              (.cons (.equal certificate) (.nil .equalTerminal)))),
          .equal certificate⟩
      | .mismatch residual => ⟨.mismatch,
          .cons .begin (.cons (.whole whole)
            (.cons (.codeReady code)
              (.cons (.mismatch residual) (.nil .mismatchTerminal)))),
          .mismatch residual⟩

def run {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (input : Input C ctx) : ExecutionResult C ctx := runReference C ctx input

end StructuralExhaustion.CT16
