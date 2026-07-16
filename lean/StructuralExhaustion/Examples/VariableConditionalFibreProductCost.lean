import StructuralExhaustion.Core.VariableConditionalFibreProductCost

namespace StructuralExhaustion.Examples.VariableConditionalFibreProductCost

open StructuralExhaustion.Core
open StructuralExhaustion.Core.FiniteSequentialFiltration
open StructuralExhaustion.Core.VariableConditionalFibreProductCost

/-! A non-graph transfer fixture with three genuinely different cost pairs. -/

def accepts (coordinate : Fin 3) (state : Fin 8) : Bool :=
  match coordinate.1 with
  | 0 => decide (4 ≤ state.1)
  | 1 => decide (state.1 % 2 = 0)
  | _ => decide (state.1 = 6)

def safe (coordinate : Fin 3) : Nat :=
  match coordinate.1 with
  | 0 => 2
  | 1 => 3
  | _ => 5

def flat (coordinate : Fin 3) : Nat :=
  match coordinate.1 with
  | 0 => 1
  | 1 => 2
  | _ => 4

@[implicit_reducible] def states : FinEnum (Fin 8) := inferInstance
@[implicit_reducible] def coordinates : FinEnum (Fin 3) := inferInstance

def profile : VariableConditionalFibreProductCost.Profile where
  State := Fin 8
  Coordinate := Fin 3
  states := states.toOrderedCollection
  coordinates := coordinates.toOrderedCollection
  accepts := accepts
  safe := safe
  flat := flat

def completeLedger : CompleteLedger profile.states.values profile.barriers :=
  .cons (by native_decide)
    (.cons (by native_decide)
      (.cons (by native_decide) (.nil _)))

theorem run_complete : profile.run = Outcome.complete completeLedger := by
  rfl

theorem final_fibre_length : completeLedger.finalStates.length = 1 := by
  native_decide

theorem variable_products :
    profile.safeProduct = 30 ∧ profile.flatProduct = 8 := by
  native_decide

/-- The generic telescope uses all three variable factor pairs. -/
theorem product_cost :
    profile.safeProduct * completeLedger.finalStates.length ≤
      profile.flatProduct * profile.states.values.length :=
  profile.complete_product_le completeLedger

/-- The shrinking fibres have sizes `8`, `4`, and `2`, so only fourteen local
predicate evaluations are performed, below the generic `8 * 3` bound. -/
theorem exact_checks : profile.checks = 14 := by
  native_decide

theorem checks_bounded : profile.checks ≤
    profile.states.values.length * profile.coordinates.values.length :=
  profile.checks_le_state_mul_coordinate

end StructuralExhaustion.Examples.VariableConditionalFibreProductCost
