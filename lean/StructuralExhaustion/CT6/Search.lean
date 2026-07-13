import StructuralExhaustion.CT6.State

namespace StructuralExhaustion.CT6

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

inductive ActivityDecision where
  | firstFailure (residual : FirstFailureResidual S capability input)
  | active (residual : ActiveLedgerResidual S capability input)

/-- Search the declared finite order and retain the no-earlier-failure proof. -/
def analyzeActivity : ActivityDecision S capability input :=
  match Core.FiniteSearch.first capability.failureOrder (S.Failure input)
      (capability.failureDecidable input) with
  | .found hit => .firstFailure {
      hit := hit
      data := S.failureData input hit.value hit.holds
      data_eq := rfl
    }
  | .absent absent => .active {
      noFailure := fun index => absent index
        (capability.failureOrder.mem_orderedValues index)
      total := activeTotal S capability input
      computed := rfl
    }

theorem analyzeActivity_sound :
    match analyzeActivity S capability input with
    | .firstFailure residual =>
        S.Failure input residual.hit.value ∧
          (∀ candidate, candidate ∈ residual.hit.before →
            ¬ S.Failure input candidate)
    | .active _ => ∀ index, ¬ S.Failure input index := by
  cases analyzeActivity S capability input with
  | firstFailure residual => exact ⟨residual.hit.holds,
      residual.hit.beforeAbsent⟩
  | active residual => exact residual.noFailure

end StructuralExhaustion.CT6
