import StructuralExhaustion.Core.FiniteTriangle

namespace StructuralExhaustion.Examples.FiniteTriangle

open Core

/-! A theorem-independent fixture for the symbolic strict-triangle count. -/

theorem fourTriangle_card :
    Fintype.card (Core.FiniteTriangle.Pair 4) = 10 := by
  rw [Core.FiniteTriangle.card_eq_sum]
  decide

theorem fourTriangle_natCard :
    Nat.card (Core.FiniteTriangle.Pair 4) = 10 := by
  rw [Core.FiniteTriangle.natCard_eq_sum]
  decide

#print axioms fourTriangle_card
#print axioms fourTriangle_natCard

end StructuralExhaustion.Examples.FiniteTriangle
