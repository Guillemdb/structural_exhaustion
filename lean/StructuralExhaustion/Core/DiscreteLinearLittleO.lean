import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StructuralExhaustion.Core.DiscreteLinearLittleO

open Filter Asymptotics

/-- Every fixed linear envelope is little-o of `n log n` along the natural
numbers. -/
theorem const_mul_natCast_isLittleO_natCast_mul_log (constant : ℝ) :
    (fun n : Nat => constant * (n : ℝ)) =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have logarithm :
      (fun _n : Nat => constant) =o[atTop]
        (fun n : Nat => Real.log (n : ℝ)) :=
    Real.isLittleO_const_log_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have linear := isBigO_refl (fun n : Nat => (n : ℝ)) atTop
  simpa [mul_comm] using logarithm.mul_isBigO linear

/-- Any real sequence eventually bounded in norm by a fixed linear envelope
is little-o of `n log n`. -/
theorem isLittleO_natCast_mul_log_of_eventually_le_linear
    (sequence : Nat → ℝ) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ᶠ n in atTop, ‖sequence n‖ ≤ constant * (n : ℝ)) :
    sequence =o[atTop] (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have bigO : sequence =O[atTop] (fun n : Nat => constant * (n : ℝ)) := by
    have bigOWith : IsBigOWith 1 atTop sequence
        (fun n : Nat => constant * (n : ℝ)) := by
      apply isBigOWith_iff.2
      filter_upwards [bound] with n hn
      simpa [norm_mul, abs_of_nonneg constantNonnegative] using hn
    exact bigOWith.isBigO
  exact bigO.trans_isLittleO (const_mul_natCast_isLittleO_natCast_mul_log constant)

end StructuralExhaustion.Core.DiscreteLinearLittleO
