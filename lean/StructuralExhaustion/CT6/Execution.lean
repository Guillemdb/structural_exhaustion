import StructuralExhaustion.CT6.Graph

namespace StructuralExhaustion.CT6

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

inductive RawOutcome : Graph.Terminal → Type _ where
  | firstFailure (residual : FirstFailureResidual S capability input) :
      RawOutcome .firstFailure
  | activeLedger (residual : ActiveLedgerResidual S capability input) :
      RawOutcome .activeLedger

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability input .entry terminal.nodeId
  outcome : RawOutcome S capability input terminal
namespace ExecutionResult
def trace (result : ExecutionResult S capability input) := result.path.trace
end ExecutionResult

def runReference : ExecutionResult S capability input :=
  match analyzeActivity S capability input with
  | .firstFailure residual => {
      terminal := .firstFailure
      path := .cons .beginSearch
        (.cons (.failure residual) (.nil .firstFailureTerminal))
      outcome := .firstFailure residual
    }
  | .active residual => {
      terminal := .activeLedger
      path := .cons .beginSearch
        (.cons (.active residual) (.nil .activeLedgerTerminal))
      outcome := .activeLedger residual
    }

def run := runReference S capability input

end StructuralExhaustion.CT6
