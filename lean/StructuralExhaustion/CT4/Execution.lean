import StructuralExhaustion.CT4.Graph

namespace StructuralExhaustion.CT4

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)
inductive RawOutcome : Graph.Terminal → Type _ where
  | missing (residual : MissingPayerResidual S input) : RawOutcome .missing
  | overload (residual : OverloadedFibreResidual S capability input) :
      RawOutcome .overload
  | c4 (certificate : C4Certificate S capability input) : RawOutcome .c4
  | capacity (residual : CapacityResidual S capability input) : RawOutcome .capacity
structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability input .entry terminal.nodeId
  outcome : RawOutcome S capability input terminal
namespace ExecutionResult
def trace (result : ExecutionResult S capability input) := result.path.trace
end ExecutionResult

def runReference : ExecutionResult S capability input :=
  let assignment := assignmentState S capability input
  match analyzeAvailability S capability input assignment with
  | .missing residual => {
      terminal := .missing
      path := .cons .beginAssignment
        (.cons (.assigned assignment)
          (.cons (.missing residual) (.nil .missingTerminal)))
      outcome := .missing residual
    }
  | .total total =>
      match analyzeFibres S capability input total with
      | .overloaded residual => {
          terminal := .overload
          path := .cons .beginAssignment
            (.cons (.assigned assignment)
              (.cons (.total total)
                (.cons (.overloaded residual) (.nil .overloadTerminal))))
          outcome := .overload residual
        }
      | .bounded bounded =>
          match compareCapacity S capability input bounded with
          | .closes certificate => {
              terminal := .c4
              path := .cons .beginAssignment
                (.cons (.assigned assignment)
                  (.cons (.total total)
                    (.cons (.bounded bounded)
                      (.cons (.c4 certificate) (.nil .c4Terminal)))))
              outcome := .c4 certificate
            }
          | .residual residual => {
              terminal := .capacity
              path := .cons .beginAssignment
                (.cons (.assigned assignment)
                  (.cons (.total total)
                    (.cons (.bounded bounded)
                      (.cons (.capacity residual) (.nil .capacityTerminal)))))
              outcome := .capacity residual
            }

def run := runReference S capability input

end StructuralExhaustion.CT4
