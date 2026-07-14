import StructuralExhaustion.Core.FiniteRefinedLedger
import StructuralExhaustion.Core.FiniteWeightedSelection

namespace StructuralExhaustion.Core.DependentWeightedSelection

universe uDemand uItem uCarrier

/-!
# Dependent finite weighted candidate families

This adapter is the safe bridge from concrete local weighted selections to a
refined-ledger profile.  Applications provide only the literal item type and
weighted selection profile at each demand.  Candidate types, their finiteness,
and carrier supports are all derived by the framework.
-/

structure Profile (Demand : Type uDemand) (Carrier : Type uCarrier) where
  Item : Demand → Type uItem
  demands : FinEnum Demand
  selection : (demand : Demand) →
    FiniteWeightedSelection.Profile (Item demand) Carrier

namespace Profile

variable {Demand : Type uDemand} {Carrier : Type uCarrier}
variable (profile : Profile.{uDemand, uItem, uCarrier} Demand Carrier)

abbrev Candidate (demand : Demand) :=
  (profile.selection demand).Candidate

/-- The derived refined ledger has no application-supplied candidate or
support field. -/
noncomputable def refinedLedger :
    FiniteRefinedLedger.Profile.{uDemand, uItem, uCarrier} Demand Carrier where
  Candidate := profile.Candidate
  demands := profile.demands
  finiteCandidates := fun demand =>
    FiniteWeightedSelection.Profile.finite_candidate_fibre
      (profile.selection demand)
  carrierSupport := fun demand candidate =>
    (profile.selection demand).carrierSupport candidate
  demandSupport := fun demand =>
    (profile.selection demand).declaredCarrierSupport
  carrierSupport_subset := fun demand candidate =>
    (profile.selection demand).carrierSupport_subset_declared candidate

theorem candidate_finite (demand : Demand) :
    Finite (profile.Candidate demand) :=
  FiniteWeightedSelection.Profile.finite_candidate_fibre
    (profile.selection demand)

@[simp]
theorem refinedLedger_demands : profile.refinedLedger.demands = profile.demands :=
  rfl

@[simp]
theorem refinedLedger_carrierSupport (demand : Demand)
    (candidate : profile.Candidate demand) :
    profile.refinedLedger.carrierSupport demand candidate =
      (profile.selection demand).carrierSupport candidate :=
  rfl

@[simp]
theorem refinedLedger_demandSupport (demand : Demand) :
    profile.refinedLedger.demandSupport demand =
      (profile.selection demand).declaredCarrierSupport :=
  rfl

end Profile

end StructuralExhaustion.Core.DependentWeightedSelection
