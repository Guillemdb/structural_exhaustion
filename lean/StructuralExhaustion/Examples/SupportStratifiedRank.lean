import StructuralExhaustion.CT15.SupportStratifiedRank
import StructuralExhaustion.Examples.SupportStratifiedDetermination

namespace StructuralExhaustion.Examples.SupportStratifiedRank

open StructuralExhaustion
open StructuralExhaustion.Examples.SupportStratifiedDetermination

def certificate (basisCoordinate determined : Bool)
    (distinct : basisCoordinate ≠ determined) : profile.Certificate where
  original := .atom
  carrier := .carrier
  original_eligible := rfl
  original_le_carrier := Or.inr ⟨rfl, rfl⟩
  carrier_connected := trivial
  determined := determined
  basisCoordinate := basisCoordinate
  distinct := distinct
  original_carries_determined := trivial
  original_carries_basis := trivial
  carrier_carries_determined := trivial
  carrier_carries_basis := trivial
  carrier_determines := rfl
  quotientCode := fun _ => 0
  identified := rfl
  carrierBoundary := ()
  carrierBoundary_eq := rfl
  originalBoundary := ()
  originalBoundary_eq := rfl
  originalQuotientCode := fun _ => 0
  quotientRestriction := rfl
  originalIdentified := rfl
  carrierUniversal := by intro context; cases context; rfl
  representative := ()
  minimal := by
    intro support _ determines _support_le
    cases support with
    | atom => cases determines
    | carrier => exact Or.inl rfl

def candidate : CT15.SupportStratifiedRank.Candidate profile where
  quotientCode := fun _ => 0
  carrier := .carrier
  certify := fun basis determined distinct _identified =>
    certificate basis determined distinct
  certify_code := by intros; rfl
  certify_basis := by intros; rfl
  certify_determined := by intros; rfl
  certify_carrier := by intros; rfl

@[implicit_reducible]
def coordinates : FinEnum Bool := Core.Enumeration.bool

def rankProfile := CT15.SupportStratifiedRank.profile profile coordinates

theorem strictRankDrop : rankProfile.targetRank < rankProfile.coordinates.card := by
  have upper : rankProfile.targetRank ≤ 1 := by
    obtain ⟨family, survives, cardEq⟩ :=
      rankProfile.exists_surviving_card_eq_targetRank
    rw [← cardEq]
    apply Finset.card_le_one.mpr
    intro left leftMem right rightMem
    exact survives.2 candidate leftMem rightMem (by rfl)
  have cardTwo : rankProfile.coordinates.card = 2 := by decide
  omega

noncomputable def circuit : rankProfile.PairCircuit :=
  rankProfile.pairCircuitOfRankDrop strictRankDrop

/-- The rank drop retains a real support certificate and routes it without
identifying the carrier and atom context universes. -/
theorem circuit_routes :
    Nonempty (CT15.SupportStratifiedRank.Profile.certificate rankProfile circuit).Routed :=
  (CT15.SupportStratifiedRank.Profile.certificate rankProfile circuit).route_total

end StructuralExhaustion.Examples.SupportStratifiedRank
