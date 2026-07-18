import StructuralExhaustion.Core.FiniteExactStateCorridor

namespace StructuralExhaustion.Examples.FiniteExactStateCorridor

open StructuralExhaustion

def stages : Core.OrderedCollection (Fin 4) :=
  ⟨[0, 1, 2, 3], by decide, inferInstance⟩

def profile : Core.FiniteExactStateCorridor.Profile (Fin 4) (Fin 3) where
  stages := stages
  stateBound := 3
  encode := id
  encode_injective := Function.injective_id
  code stage := ⟨stage.val % 3, Nat.mod_lt _ (by decide)⟩

theorem run_is_repeated : ∃ repetition, profile.run = .repeated repetition := by
  rcases profile.run_total with terminal | repeated
  · rcases terminal with ⟨short, _equation⟩
    simp [profile, stages] at short
  · exact repeated

theorem repeated_code_is_exact (repetition : profile.Repeated) :
    profile.code repetition.first = profile.code repetition.second :=
  repetition.equalCode

end StructuralExhaustion.Examples.FiniteExactStateCorridor
