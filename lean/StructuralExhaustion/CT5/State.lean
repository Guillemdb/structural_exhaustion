import StructuralExhaustion.CT5.Capability

namespace StructuralExhaustion.CT5

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

def NoSupportingWitness (site : S.Site) : Prop :=
  ∀ witness : S.Witness site, ¬ S.Supports input site witness

def DeficitAt (site : S.Site) : Prop :=
  S.Active input site ∧ NoSupportingWitness S input site

/-- A concrete active site at which the exact witness universe is empty of
supporting witnesses. -/
structure LocalDeficitResidual where
  site : S.Site
  active : S.Active input site
  noWitness : NoSupportingWitness S input site

/-- Deterministic contribution of one site: the first supporting witness in
the declared enumeration contributes, and all other cases contribute zero. -/
def contributionAt (site : S.Site) : Nat :=
  match capability.activeDecidable input site with
  | .isFalse _ => 0
  | .isTrue _ =>
      match Core.FiniteSearch.search (capability.witnesses site)
          (S.Supports input site) (capability.supportsDecidable input site) with
      | .found witness _ => S.contribution input site witness
      | .absent _ => 0

def ledgerTotal : Nat :=
  capability.sites.orderedValues.foldl
    (fun total site => total + contributionAt S capability input site) 0

/-- Exhaustive deficit exclusion emitted by the search node. -/
structure DeficitFreeState : Prop where
  complete : ∀ site, site ∈ capability.sites.orderedValues
  noDeficit : ∀ site, ¬ DeficitAt S input site

/-- Complete local ledger computed only after exhaustive deficit exclusion. -/
structure LocalLedgerState where
  deficitFree : DeficitFreeState S capability input
  total : Nat
  computed : total = ledgerTotal S capability input

def computeLedger (deficitFree : DeficitFreeState S capability input) :
    LocalLedgerState S capability input where
  deficitFree := deficitFree
  total := ledgerTotal S capability input
  computed := rfl

/-- Arithmetic C4 certificate; the global lower bound strictly exceeds the
available capacity. -/
structure C4Certificate where
  ledger : LocalLedgerState S capability input
  capacity_lt_required : capability.capacity input < capability.required input

/-- A bounded charge ledger ready for the charging layer. -/
structure ChargeLedgerResidual where
  ledger : LocalLedgerState S capability input
  total_le_capacity : ledger.total ≤ capability.capacity input

/-- A computed aggregate exceeding capacity without a global C4 lower-bound
contradiction. -/
structure AggregateResidual where
  ledger : LocalLedgerState S capability input
  required_le_capacity : capability.required input ≤ capability.capacity input
  capacity_lt_total : capability.capacity input < ledger.total

end StructuralExhaustion.CT5
