import StructuralExhaustion.Core.PoweredJointNormalization

namespace StructuralExhaustion.Examples.PoweredJointNormalization

open StructuralExhaustion

/-- A small non-Erdős fixture: two paid binary digits and one restored error
digit fit into a four-state capacity. -/
def boolPairProfile : Core.PoweredJointNormalization.Profile where
  stateCount := 1
  base := 2
  exponent := 1
  paidExponent := 2
  desiredExponent := 3
  errorExponent := 1
  capacity := 4
  paidCapacity := by norm_num
  desiredExact := by norm_num

example : 1 ^ 1 * 2 ^ 3 ≤ 4 ^ 1 * 2 ^ 1 :=
  boolPairProfile.withError

example :
    (boolPairProfile.exponent : ℝ) * Real.logb 2 boolPairProfile.stateCount +
        (boolPairProfile.desiredExponent : ℝ) *
          Real.logb 2 boolPairProfile.base ≤
      (boolPairProfile.exponent : ℝ) * Real.logb 2 boolPairProfile.capacity +
        (boolPairProfile.errorExponent : ℝ) *
          Real.logb 2 boolPairProfile.base :=
  boolPairProfile.logb_withError
    (by norm_num [boolPairProfile])
    (by norm_num [boolPairProfile])
    (by norm_num [boolPairProfile])

example : boolPairProfile.checks = 0 := by simp

end StructuralExhaustion.Examples.PoweredJointNormalization
