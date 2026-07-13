import StructuralExhaustion.CT9.Graph

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem uLabel
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
variable (input : Input capability)

inductive Outcome : Graph.Terminal → Type _ where
  | overloaded (residual : OverloadResidual capability input) : Outcome .overloaded
  | bounded (certificate : BoundedCertificate capability input) : Outcome .bounded

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path capability input .entry terminal.nodeId
  outcome : Outcome capability input terminal
namespace ExecutionResult
def trace (result : ExecutionResult capability input) := result.path.trace
end ExecutionResult

def runReference : ExecutionResult capability input :=
  match analyze capability input with
  | .overloaded residual =>
      ⟨.overloaded,
        .cons .begin (.cons .partitioned
          (.cons (.overloaded residual) (.nil .overloadedTerminal))),
        .overloaded residual⟩
  | .bounded certificate =>
      ⟨.bounded,
        .cons .begin (.cons .partitioned
          (.cons (.bounded certificate) (.nil .boundedTerminal))),
        .bounded certificate⟩

def run : ExecutionResult capability input := runReference capability input

end StructuralExhaustion.CT9
