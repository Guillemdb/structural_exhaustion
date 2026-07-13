import StructuralExhaustion.CT5.Graph

namespace StructuralExhaustion.CT5

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

inductive RawOutcome : Graph.Terminal → Type _ where
  | deficit (residual : LocalDeficitResidual S input) :
      RawOutcome .deficit
  | c4 (certificate : C4Certificate S capability input) : RawOutcome .c4
  | charge (residual : ChargeLedgerResidual S capability input) :
      RawOutcome .charge
  | aggregate (residual : AggregateResidual S capability input) :
      RawOutcome .aggregate

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability input .entry terminal.nodeId
  outcome : RawOutcome S capability input terminal

namespace ExecutionResult
def trace (result : ExecutionResult S capability input) := result.path.trace
end ExecutionResult

def runReference : ExecutionResult S capability input :=
  match analyzeDeficit S capability input with
  | .deficit residual => {
      terminal := .deficit
      path := .cons .beginDeficit
        (.cons (.deficitFound residual) (.nil .deficitTerminal))
      outcome := .deficit residual
    }
  | .clear deficitFree =>
      let ledger := computeLedger S capability input deficitFree
      match compare S capability input ledger with
      | .closes certificate => {
          terminal := .c4
          path := .cons .beginDeficit
            (.cons (.deficitAbsent deficitFree)
              (.cons (.summed ledger)
                (.cons (.comparisonC4 certificate) (.nil .c4Terminal))))
          outcome := .c4 certificate
        }
      | .charge residual => {
          terminal := .charge
          path := .cons .beginDeficit
            (.cons (.deficitAbsent deficitFree)
              (.cons (.summed ledger)
                (.cons (.comparisonCharge residual) (.nil .chargeTerminal))))
          outcome := .charge residual
        }
      | .aggregate residual => {
          terminal := .aggregate
          path := .cons .beginDeficit
            (.cons (.deficitAbsent deficitFree)
              (.cons (.summed ledger)
                (.cons (.comparisonAggregate residual) (.nil .aggregateTerminal))))
          outcome := .aggregate residual
        }

def run := runReference S capability input

end StructuralExhaustion.CT5
