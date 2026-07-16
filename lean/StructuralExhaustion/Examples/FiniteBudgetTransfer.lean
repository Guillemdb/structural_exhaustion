import StructuralExhaustion.Core.FiniteBudgetTransfer

namespace StructuralExhaustion.Examples.FiniteBudgetTransfer

open StructuralExhaustion

/-! A fixed transfer fixture, independent of any graph application. -/

example : 4 * 7 < 31 := by
  exact Core.FiniteBudgetTransfer.strict_scaled_of_le_of_lt_of_le
    (actual := 7) (upper := 7) (floor := 29) (total := 31) (scale := 4)
    (by decide) (by decide) (by decide)

end StructuralExhaustion.Examples.FiniteBudgetTransfer
