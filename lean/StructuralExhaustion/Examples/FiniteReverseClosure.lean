import StructuralExhaustion.Core.FiniteReverseClosure

namespace StructuralExhaustion.Examples.FiniteReverseClosure

open StructuralExhaustion.Core.FiniteReverseClosure

def closedProfile : Profile (Fin 4) (Fin 4) where
  items := [0, 1, 2, 3]
  nodup := by native_decide
  key := id
  reverse
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  keyDecidableEq := inferInstance
  keyInjective := by intro left right _ _ equal; exact equal
  reverse_ne := by intro item member; fin_cases item <;> decide

example : closedProfile.closedItems.length ≤
    2 * closedProfile.pairLabels.length :=
  closedProfile.closedItems_le_two_mul_pairLabels

def missingProfile : Profile (Fin 3) (Fin 4) where
  items := [0, 1, 2]
  nodup := by native_decide
  key := fun item => ⟨item, by omega⟩
  reverse
    | 0 => 1 | 1 => 0 | 2 => 3
  keyDecidableEq := inferInstance
  keyInjective := by
    intro left right _ _ equal
    apply Fin.ext
    exact congrArg (fun value : Fin 4 => value.val) equal
  reverse_ne := by intro item member; fin_cases item <;> decide

example : ∃ hit : Core.FiniteSearch.FirstHit missingProfile.items
    (fun item => ¬ missingProfile.reversePresent item), True := by
  refine ⟨{
    before := [0, 1]
    value := 2
    after := []
    split := by native_decide
    holds := by
      simp [Profile.reversePresent, Profile.keys, missingProfile]
    beforeAbsent := by
      intro candidate member
      fin_cases candidate <;>
        simp_all [Profile.reversePresent, Profile.keys, missingProfile]
  }, trivial⟩

end StructuralExhaustion.Examples.FiniteReverseClosure
