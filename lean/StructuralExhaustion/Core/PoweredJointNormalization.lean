import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace StructuralExhaustion.Core.PoweredJointNormalization

/-!
# Exact error-bearing normalization of a powered joint capacity

This profile isolates the recurring symbolic step that restores discarded
local mass to an already-proved powered capacity inequality.  It performs no
enumeration and does not inspect the state families that produced the counts.
-/

/-- Exact powered capacity together with the mass omitted from its paid
exponent. -/
structure Profile where
  stateCount : Nat
  base : Nat
  exponent : Nat
  paidExponent : Nat
  desiredExponent : Nat
  errorExponent : Nat
  capacity : Nat
  paidCapacity :
    stateCount ^ exponent * base ^ paidExponent ≤ capacity ^ exponent
  desiredExact : desiredExponent = paidExponent + errorExponent

namespace Profile

/-- Restore the omitted exponent on both sides.  This is the exact finite
form of an error-bearing entropy inequality. -/
theorem withError (profile : Profile) :
    profile.stateCount ^ profile.exponent *
        profile.base ^ profile.desiredExponent ≤
      profile.capacity ^ profile.exponent *
        profile.base ^ profile.errorExponent := by
  rw [profile.desiredExact, pow_add]
  calc
    profile.stateCount ^ profile.exponent *
          (profile.base ^ profile.paidExponent *
            profile.base ^ profile.errorExponent) =
        (profile.stateCount ^ profile.exponent *
          profile.base ^ profile.paidExponent) *
            profile.base ^ profile.errorExponent := by ring
    _ ≤ profile.capacity ^ profile.exponent *
          profile.base ^ profile.errorExponent :=
      Nat.mul_le_mul_right _ profile.paidCapacity

/-- Real-logarithmic form of `withError`.  Applications supply only
positivity of the three scalar counts; the framework performs all casts,
monotonicity, product expansion, and power expansion. -/
theorem logb_withError (profile : Profile)
    (stateCountPos : 0 < profile.stateCount)
    (basePos : 0 < profile.base)
    (capacityPos : 0 < profile.capacity) :
    (profile.exponent : ℝ) * Real.logb 2 profile.stateCount +
        (profile.desiredExponent : ℝ) * Real.logb 2 profile.base ≤
      (profile.exponent : ℝ) * Real.logb 2 profile.capacity +
        (profile.errorExponent : ℝ) * Real.logb 2 profile.base := by
  have castBound :
      (profile.stateCount : ℝ) ^ profile.exponent *
          (profile.base : ℝ) ^ profile.desiredExponent ≤
        (profile.capacity : ℝ) ^ profile.exponent *
          (profile.base : ℝ) ^ profile.errorExponent := by
    exact_mod_cast profile.withError
  have logged := Real.logb_le_logb_of_le (b := (2 : ℝ))
    (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 <
      (profile.stateCount : ℝ) ^ profile.exponent *
        (profile.base : ℝ) ^ profile.desiredExponent)
    castBound
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow] at logged
  exact logged

/-- Normalization is certificate-only. -/
def checks (_profile : Profile) : Nat := 0

@[simp] theorem checks_eq_zero (profile : Profile) : profile.checks = 0 := rfl

end Profile

end StructuralExhaustion.Core.PoweredJointNormalization
