import StructuralExhaustion.CT8.Graph

namespace StructuralExhaustion.CT8

universe uAmbient uBranch uState uType uResponseContext
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)
variable (ctx : Core.BranchContext P)
variable (input : Input capability ctx)

inductive Outcome : Graph.Terminal → Type _ where
  | noRepetition (c : NoRepetitionCertificate capability ctx input) : Outcome .noRepetition
  | removal (r : RemovalResidual capability ctx input) : Outcome .removal
  | separation (r : SeparationResidual capability ctx input) : Outcome .separation
structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path capability ctx input .entry terminal.nodeId
  outcome : Outcome capability ctx input terminal
namespace ExecutionResult
def trace (r : ExecutionResult capability ctx input) := r.path.trace
end ExecutionResult

def runReference : ExecutionResult capability ctx input :=
  match findRepeated capability input.sequence with
  | .unique absent =>
      let certificate : NoRepetitionCertificate capability ctx input := ⟨absent⟩
      ⟨.noRepetition,
        .cons .begin (.cons (.unique certificate) (.nil .noRepetitionTerminal)),
        .noRepetition certificate⟩
  | .repeated pair =>
      match analyzeResponses capability ctx input pair with
      | .removable residual => ⟨.removal,
          .cons .begin (.cons (.repeated pair)
            (.cons (.removable residual) (.nil .removalTerminal))), .removal residual⟩
      | .separating residual => ⟨.separation,
          .cons .begin (.cons (.repeated pair)
            (.cons (.separating residual) (.nil .separationTerminal))),
          .separation residual⟩

def run : ExecutionResult capability ctx input := runReference capability ctx input

end StructuralExhaustion.CT8
