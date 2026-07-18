import StructuralExhaustion.Core.FiniteActiveSupportProjection

namespace StructuralExhaustion.Examples.FiniteActiveSupportProjection

open StructuralExhaustion

def profile : Core.FiniteActiveSupportProjection.Profile (Finset (Fin 5)) (Fin 5) where
  entries := [{0, 1}, {2, 3}, ∅]
  vertexDecEq := inferInstance
  support := id

def active : Finset (Fin 5) := {0, 1, 4}

example : profile.SupportedIn active ⟨0, by decide⟩ := by
  simp [Core.FiniteActiveSupportProjection.Profile.SupportedIn,
    Core.FiniteActiveSupportProjection.Profile.entry, profile, active]

example : ¬profile.SupportedIn active ⟨1, by decide⟩ := by
  intro contained
  have member : (2 : Fin 5) ∈ ({2, 3} : Finset (Fin 5)) := by simp
  have := contained member
  simpa [Core.FiniteActiveSupportProjection.Profile.SupportedIn,
    Core.FiniteActiveSupportProjection.Profile.entry, profile, active] using this

example : profile.SupportedIn active ⟨2, by decide⟩ := by
  simp [Core.FiniteActiveSupportProjection.Profile.SupportedIn,
    Core.FiniteActiveSupportProjection.Profile.entry, profile, active]

example : (profile.activeKeys active).card ≤ 3 := by
  simpa [profile] using profile.activeKeys_card_le_entries active

example (vertex : Fin 5) :
    (∃ hit, profile.classifyEndpoint vertex = .hit hit) ∨
      (∃ complete, profile.classifyEndpoint vertex = .complete complete) :=
  profile.classifyEndpoint_total vertex

end StructuralExhaustion.Examples.FiniteActiveSupportProjection
