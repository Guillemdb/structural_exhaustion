namespace StructuralExhaustion.Core.FiniteBudgetTransfer

/-!
# Exact transfer of a finite scaled budget

This arithmetic kernel applies when a local ledger is bounded by a finite
upper budget, that budget is strictly below a retained floor, and the floor is
bounded by the actual carrier size.  It contains no asymptotic notation and
does not manufacture any of the three inequalities.
-/

/-- Transfer a strict scaled cap through an upper estimate and a retained
lower floor. -/
theorem strict_scaled_of_le_of_lt_of_le
    {actual upper floor total scale : Nat}
    (actual_le_upper : actual ≤ upper)
    (upper_lt_floor : scale * upper < floor)
    (floor_le_total : floor ≤ total) :
    scale * actual < total := by
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left scale actual_le_upper) upper_lt_floor)
    floor_le_total

end StructuralExhaustion.Core.FiniteBudgetTransfer
