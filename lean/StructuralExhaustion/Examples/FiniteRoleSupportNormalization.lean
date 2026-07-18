import StructuralExhaustion.Core.FiniteRoleSupportNormalization

namespace StructuralExhaustion.Examples.FiniteRoleSupportNormalization

open StructuralExhaustion

abbrev Kind := Bool

abbrev Label := Fin 3
abbrev Value := Fin 4
abbrev Coordinate := Fin 3

def support : Coordinate → Finset (Fin 3)
  | 0 => {0}
  | 1 => {0, 1}
  | 2 => {2}

def profile : Core.FiniteRoleSupportNormalization.Profile
    (Fin 3) (Fin 3) Kind Label Value Coordinate where
  roles := FinEnum.fin
  vertexDecEq := inferInstance
  roleVertex := id
  carrier := Finset.univ
  memCarrier_iff_role := by
    intro vertex
    exact ⟨fun _ => ⟨vertex, rfl⟩, fun _ => Finset.mem_univ vertex⟩
  coordinates := FinEnum.fin
  kind coordinate := coordinate = 0
  label := id
  support := support
  supportContained := fun _ _ _ => Finset.mem_univ _
  value coordinate := ⟨coordinate.1, by omega⟩

example : Fintype.card
    (Core.FiniteRoleSupportNormalization.Profile.Code (Fin 3) Kind Label Value) =
      2 * 3 * 2 ^ 3 * 4 := by
  rw [Core.FiniteRoleSupportNormalization.Profile.code_card]
  norm_num

example {left right : Coordinate} (equal : profile.code left = profile.code right) :
    profile.structuralValue left = profile.structuralValue right :=
  profile.code_eq_implies_structuralValue_eq equal

example : profile.normalizedCodes.length ≤ 2 * 3 * 2 ^ 3 * 4 := by
  simpa using profile.normalizedCodes_length_le_symbolic

end StructuralExhaustion.Examples.FiniteRoleSupportNormalization
