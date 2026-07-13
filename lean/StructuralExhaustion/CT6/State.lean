import StructuralExhaustion.CT6.Capability

namespace StructuralExhaustion.CT6

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

def activeTotal : Nat :=
  capability.failureOrder.orderedValues.foldl
    (fun total index => total + S.contribution input index) 0

/-- Canonical first failure with its exact clean prefix and structural datum. -/
structure FirstFailureResidual where
  hit : Core.FiniteSearch.FirstHit capability.failureOrder.orderedValues
    (S.Failure input)
  data : S.FailureData
  data_eq : data = S.failureData input hit.value hit.holds

/-- Exhaustive active ledger produced when no monitored index fails. -/
structure ActiveLedgerResidual where
  noFailure : ∀ index, ¬ S.Failure input index
  total : Nat
  computed : total = activeTotal S capability input

end StructuralExhaustion.CT6
