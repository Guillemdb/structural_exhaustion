import StructuralExhaustion.Core.FiniteStructuralCutState

namespace StructuralExhaustion.Examples.FiniteStructuralCutState

open StructuralExhaustion

/-- A non-graph fixture pins the exact product count and the two reusable
bounded-corridor arithmetic constructors. -/
abbrev FixtureState := Core.FiniteStructuralCutState.State
  Bool (Fin 3) (Fin 2) (Fin 3) (Fin 4) (Fin 5)

example : Fintype.card FixtureState =
    4 ^ 2 * 2 ^ 2 * 3 ^ 2 * 2 * 3 * 4 * 5 := by
  simpa using Core.FiniteStructuralCutState.state_card
    Bool (Fin 3) (Fin 2) (Fin 3) (Fin 4) (Fin 5)

example : Core.FiniteStructuralCutState.exchangeBound 17 30 = 47 := by
  decide

example : Core.FiniteStructuralCutState.overlapDenominator 47 11 = 518 := by
  decide

end StructuralExhaustion.Examples.FiniteStructuralCutState
