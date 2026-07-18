import StructuralExhaustion.Core.FinitePriorCodeMatch

namespace StructuralExhaustion.Examples.FinitePriorCodeMatch

open StructuralExhaustion

def profile : Core.FinitePriorCodeMatch.Profile where
  Stage := Fin 5
  Code := Bool
  codeDecEq := inferInstance
  before := fun stage ↦ (List.finRange 5).take stage.val
  code := fun stage ↦ decide (stage.val % 2 = 0)

example : (∃ prior member same,
    profile.run (3 : Fin 5) = .matched prior member same) ∨
    (∃ none, profile.run (3 : Fin 5) = .absent none) :=
  profile.run_total (3 : Fin 5)

end StructuralExhaustion.Examples.FinitePriorCodeMatch
