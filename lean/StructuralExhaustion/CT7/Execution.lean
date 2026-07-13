import StructuralExhaustion.CT7.Graph

namespace StructuralExhaustion.CT7

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (ctx : Core.BranchContext P) (input : Input S ctx)
inductive RawOutcome : Graph.Terminal → Type _ where
  | realization (certificate : RealizationCertificate S capability ctx input) :
      RawOutcome .realization
  | distinguishing (residual : DistinguishingResidual S capability ctx input) :
      RawOutcome .distinguishing
  | neutral (certificate : NeutralityCertificate S capability ctx input) :
      RawOutcome .neutral
structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability ctx input .entry terminal.nodeId
  outcome : RawOutcome S capability ctx input terminal
namespace ExecutionResult
def trace (result : ExecutionResult S capability ctx input) := result.path.trace
end ExecutionResult

def runReference : ExecutionResult S capability ctx input :=
  match analyzeRealization S capability ctx input with
  | .realizing certificate => {
      terminal := .realization
      path := .cons .beginRealization
        (.cons (.realized certificate) (.nil .realizationTerminal))
      outcome := .realization certificate
    }
  | .unrealized unrealized =>
      match analyzeDistinction S capability ctx input unrealized with
      | .distinguishing residual => {
          terminal := .distinguishing
          path := .cons .beginRealization
            (.cons (.unrealized unrealized)
              (.cons (.distinguished residual) (.nil .distinguishingTerminal)))
          outcome := .distinguishing residual
        }
      | .neutral certificate => {
          terminal := .neutral
          path := .cons .beginRealization
            (.cons (.unrealized unrealized)
              (.cons (.neutral certificate) (.nil .neutralTerminal)))
          outcome := .neutral certificate
        }
def run := runReference S capability ctx input

end StructuralExhaustion.CT7
