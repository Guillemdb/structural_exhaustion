import StructuralExhaustion.CT5.State

namespace StructuralExhaustion.CT5

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

def deficitAtDecidable (site : S.Site) : Decidable (DeficitAt S input site) :=
  match capability.activeDecidable input site with
  | .isFalse inactive => .isFalse fun deficit => inactive deficit.1
  | .isTrue active =>
      match Core.FiniteSearch.search (capability.witnesses site)
          (S.Supports input site) (capability.supportsDecidable input site) with
      | .found witness supports => .isFalse fun deficit =>
          deficit.2 witness supports
      | .absent noWitness => .isTrue ⟨active, noWitness⟩

inductive DeficitDecision where
  | deficit (residual : LocalDeficitResidual S input)
  | clear (state : DeficitFreeState S capability input)

/-- Search every active site for a missing local witness. -/
def analyzeDeficit : DeficitDecision S capability input :=
  match Core.FiniteSearch.search capability.sites (DeficitAt S input)
      (deficitAtDecidable S capability input) with
  | .found site deficit => .deficit ⟨site, deficit.1, deficit.2⟩
  | .absent noDeficit => .clear
      ⟨capability.sites.mem_orderedValues, noDeficit⟩

inductive ComparisonDecision (ledger : LocalLedgerState S capability input) where
  | closes (certificate : C4Certificate S capability input)
  | charge (residual : ChargeLedgerResidual S capability input)
  | aggregate (residual : AggregateResidual S capability input)

/-- Exact arithmetic comparison with fixed branch priority. -/
def compare (ledger : LocalLedgerState S capability input) :
    ComparisonDecision S capability input ledger :=
  match Nat.decLt (capability.capacity input) (capability.required input) with
  | .isTrue capacityLtRequired => .closes ⟨ledger, capacityLtRequired⟩
  | .isFalse notCapacityLtRequired =>
      have requiredLeCapacity :
          capability.required input ≤ capability.capacity input :=
        Nat.le_of_not_gt notCapacityLtRequired
      match Nat.decLt (capability.capacity input) ledger.total with
      | .isTrue capacityLtTotal =>
          .aggregate ⟨ledger, requiredLeCapacity, capacityLtTotal⟩
      | .isFalse notCapacityLtTotal =>
          .charge ⟨ledger, Nat.le_of_not_gt notCapacityLtTotal⟩

theorem analyzeDeficit_sound :
    match analyzeDeficit S capability input with
    | .deficit residual => DeficitAt S input residual.site
    | .clear _ => ∀ site, ¬ DeficitAt S input site := by
  cases analyzeDeficit S capability input with
  | deficit residual => exact ⟨residual.active, residual.noWitness⟩
  | clear state => exact state.noDeficit

end StructuralExhaustion.CT5
