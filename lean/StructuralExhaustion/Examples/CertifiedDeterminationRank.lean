import StructuralExhaustion.CT15.CertifiedDeterminationRank
import StructuralExhaustion.Core.SupportStratifiedDetermination

namespace StructuralExhaustion.Examples.CertifiedDeterminationRank

open StructuralExhaustion

def system : CT15.CertifiedDeterminationRank.System where
  Coordinate := Bool
  Candidate := Unit
  code := fun _ _ => 0

@[implicit_reducible]
def coordinates : FinEnum Bool := Core.Enumeration.bool

def profile : CT15.CertifiedDeterminationRank.Profile system where
  coordinates := coordinates

theorem strictRankDrop : profile.targetRank < profile.coordinates.card := by
  have upper : profile.targetRank ≤ 1 := by
    obtain ⟨family, survives, cardEq⟩ :=
      profile.exists_surviving_card_eq_targetRank
    rw [← cardEq]
    apply Finset.card_le_one.mpr
    intro left leftMem right rightMem
    exact survives.2 () leftMem rightMem (by rfl)
  have cardTwo : profile.coordinates.card = 2 := by decide
  omega

noncomputable def circuit : profile.PairCircuit :=
  profile.pairCircuitOfRankDrop strictRankDrop

theorem circuit_retains_candidate : circuit.candidate = () := by
  cases circuit.candidate
  rfl

end StructuralExhaustion.Examples.CertifiedDeterminationRank
