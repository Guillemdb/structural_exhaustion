import Mathlib.Tactic

namespace StructuralExhaustion.Core.StrictGapAbsorption

/-!
# Strict gap absorption

This module owns the reusable arithmetic step behind manuscript arguments of
the form

`quantity / scale ≤ main + o(1)` and `main < threshold`.

Applications provide only the concrete quantity, scale, coefficient, and the
already-produced small-error certificate.  The framework performs the
strict-gap conversion and the common scaled-integer consequences.
-/

/-- A pointwise small-error certificate for a strict coefficient gap.  In an
asymptotic proof this is the finite tail instance obtained from the reusable
eventual theorem; in a finite proof it can be supplied by an explicit threshold
calculation. -/
structure ErrorWithinGap (main threshold scale error : ℝ) : Prop where
  error_lt_gap_mul_scale : error < (threshold - main) * scale

/-- A framework marker that a concrete finite error term is one of the
small-o errors covered by the global sufficiently-large tail of an
asymptotic proof.  The marker records the strict coefficient gap; the root
tail certificate turns such registered requests into pointwise
`ErrorWithinGap` facts for the current residual. -/
structure TailSmallError (main threshold scale error : ℝ) : Prop where
  gap_pos : 0 < threshold - main

/-- Global "large enough" selector for asymptotic arguments.  It is attached
once to the root residual and then propagated by the residual ledger.  Node
implementations register only concrete strict-gap requests; this framework
certificate performs the paper's standard finite-tail specialization. -/
structure LargeEnoughTail : Prop where
  withinGap :
    ∀ {main threshold scale error : ℝ},
      TailSmallError main threshold scale error →
        ErrorWithinGap main threshold scale error

/-- Absorb a pointwise error term into a strict coefficient gap. -/
theorem normalized_lt_threshold
    {quantity scale error main threshold : ℝ}
    (scale_pos : 0 < scale)
    (cap : quantity ≤ main * scale + error)
    (_gap : main < threshold)
    (small : ErrorWithinGap main threshold scale error) :
    quantity / scale < threshold := by
  have absorbed : quantity < threshold * scale := by
    calc
      quantity ≤ main * scale + error := cap
      _ < main * scale + (threshold - main) * scale := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_lt_add_left small.error_lt_gap_mul_scale (main * scale)
      _ = threshold * scale := by ring
  exact (div_lt_iff₀ scale_pos).mpr absorbed

/-- Natural-number version of `normalized_lt_threshold`. -/
theorem nat_normalized_lt_threshold
    {quantity scale error : Nat} {main threshold : ℝ}
    (scale_pos : 0 < (scale : ℝ))
    (cap : (quantity : ℝ) ≤ main * (scale : ℝ) + (error : ℝ))
    (_gap : main < threshold)
    (small : ErrorWithinGap main threshold (scale : ℝ) (error : ℝ)) :
    (quantity : ℝ) / (scale : ℝ) < threshold :=
  normalized_lt_threshold scale_pos cap _gap small

/-- Convert a strict normalized reciprocal bound to the denominator-free
natural-number form. -/
theorem denom_mul_lt_of_normalized_lt_inv
    {denom quantity scale : Nat}
    (denom_pos : 0 < denom)
    (scale_pos : 0 < scale)
    (strict : (quantity : ℝ) / (scale : ℝ) <
      (1 / (denom : ℝ) : ℝ)) :
    denom * quantity < scale := by
  have scale_pos_real : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have denom_pos_real : (0 : ℝ) < denom := by exact_mod_cast denom_pos
  rw [div_lt_iff₀ scale_pos_real] at strict
  have scaledReal : (denom : ℝ) * (quantity : ℝ) < (scale : ℝ) := by
    rw [one_div] at strict
    calc
      (denom : ℝ) * (quantity : ℝ) <
          (denom : ℝ) * ((denom : ℝ)⁻¹ * (scale : ℝ)) :=
        mul_lt_mul_of_pos_left strict denom_pos_real
      _ = (scale : ℝ) := by
        field_simp [ne_of_gt denom_pos_real]
  have scaled : ((denom * quantity : Nat) : ℝ) < (scale : ℝ) := by
    norm_num
    exact scaledReal
  exact_mod_cast scaled

/-- A strict scaled natural bound gives the corresponding negative signed
budget expression. -/
theorem scaled_charge_negative_of_mul_lt
    {budget quantity scale : Nat}
    (strict : budget * quantity < scale) :
    (budget : Int) * (quantity : Int) - (scale : Int) < 0 := by
  omega

/-- Combined pointwise absorption specialized to a reciprocal threshold and
signed budget expression. -/
theorem scaled_charge_negative
    {budget quantity scale error : Nat} {main : ℝ}
    (budget_pos : 0 < budget)
    (scale_pos : 0 < scale)
    (cap : (quantity : ℝ) ≤ main * (scale : ℝ) + (error : ℝ))
    (gap : main < (1 / (budget : ℝ) : ℝ))
    (small : ErrorWithinGap main (1 / (budget : ℝ) : ℝ)
      (scale : ℝ) (error : ℝ)) :
    (budget : Int) * (quantity : Int) - (scale : Int) < 0 := by
  exact scaled_charge_negative_of_mul_lt
    (denom_mul_lt_of_normalized_lt_inv budget_pos scale_pos
      (nat_normalized_lt_threshold
        (show 0 < (scale : ℝ) by exact_mod_cast scale_pos)
        cap gap small))

/-- Convert a strict normalized quarter bound to the denominator-free
natural-number form used by net-charge nodes. -/
theorem four_mul_lt_of_normalized_lt_quarter
    {quantity scale : Nat}
    (scale_pos : 0 < scale)
    (strict : (quantity : ℝ) / (scale : ℝ) < (1 / 4 : ℝ)) :
    4 * quantity < scale :=
  denom_mul_lt_of_normalized_lt_inv (by norm_num) scale_pos strict

/-- If a natural numerator is strictly below one quarter of the scale, then
the corresponding quarter-scaled signed charge is negative. -/
theorem quarter_charge_negative_of_four_mul_lt
    {quantity scale : Nat}
    (strict : 4 * quantity < scale) :
    4 * (quantity : Int) - (scale : Int) < 0 :=
  scaled_charge_negative_of_mul_lt strict

/-- Combined pointwise absorption specialized to the quarter-scaled signed
charge. -/
theorem quarter_charge_negative
    {quantity scale error : Nat} {main : ℝ}
    (scale_pos : 0 < scale)
    (cap : (quantity : ℝ) ≤ main * (scale : ℝ) + (error : ℝ))
    (gap : main < (1 / 4 : ℝ))
    (small : ErrorWithinGap main (1 / 4 : ℝ) (scale : ℝ) (error : ℝ)) :
    4 * (quantity : Int) - (scale : Int) < 0 :=
  scaled_charge_negative (budget := 4) (by norm_num) scale_pos cap gap small

/-- Signed scaled-charge nonnegativity contradicts a strict negative charge
for the corresponding natural subtraction.  This is the reusable bridge
between a finite cap proved for `a - b` as a natural numerator and a
manuscript signed integer expression. -/
theorem signed_nonnegative_false_of_nat_sub_scaled_negative
    {budget a b scale : Nat}
    (negative :
      (budget : Int) * (((a - b : Nat) : Int)) - (scale : Int) < 0)
    (nonnegative :
      0 ≤ (budget : Int) * ((a : Int) - (b : Int)) - (scale : Int)) :
    False := by
  by_cases h : b ≤ a
  · have natSub_eq : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
      omega
    rw [natSub_eq] at negative
    omega
  · have intDiff_neg : (a : Int) - (b : Int) < 0 := by omega
    have natSub_zero : a - b = 0 := by
      exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)
    have scale_pos : (0 : Int) < (scale : Int) := by
      rw [natSub_zero] at negative
      simp at negative
      omega
    have scale_nonneg : (0 : Int) ≤ (scale : Int) := by exact_mod_cast scale.zero_le
    have budget_nonneg : (0 : Int) ≤ (budget : Int) := by exact_mod_cast budget.zero_le
    have product_nonpos :
        (budget : Int) * ((a : Int) - (b : Int)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos budget_nonneg intDiff_neg.le
    have charge_neg :
        (budget : Int) * ((a : Int) - (b : Int)) - (scale : Int) < 0 := by
      omega
    omega

/-- Quarter specialization of
`signed_nonnegative_false_of_nat_sub_scaled_negative`. -/
theorem signed_nonnegative_false_of_nat_sub_quarter_negative
    {a b scale : Nat}
    (negative : 4 * (((a - b : Nat) : Int)) - (scale : Int) < 0)
    (nonnegative : 0 ≤ 4 * ((a : Int) - (b : Int)) - (scale : Int)) :
    False :=
  signed_nonnegative_false_of_nat_sub_scaled_negative
    (budget := 4) negative nonnegative

end StructuralExhaustion.Core.StrictGapAbsorption
