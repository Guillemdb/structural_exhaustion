import StructuralExhaustion.Core.FixedPointRepeatedSquareLower

namespace StructuralExhaustion.Examples.FixedPointRepeatedSquareLower

open StructuralExhaustion.Core.FixedPointRepeatedSquareLower

/-- A one-row non-Erdős transfer: `3/2` starts as `150/100`; after one
square and one binary shift the downward-rounded numerator is `112`, proving
`2 * 112/100 <= (3/2)^2`. -/
def exampleRun : Run 100 150 0 := Run.ofShifts 100 150 0 [1]

example :
    (2 : ℚ) ^ exampleRun.finalExponent * (exampleRun.finalLower : ℚ) / 100 ≤
      ((3 : ℚ) / 2) ^ (2 ^ exampleRun.steps) := by
  apply exampleRun.sound
  · norm_num
  · norm_num
  · norm_num

example : exampleRun.steps = 1 ∧ exampleRun.finalExponent = 1 ∧
    exampleRun.finalLower = 112 := by
  native_decide

/-- The powered-state conversion is independent of the Erdős constants.
Here `3/2` has certified rate `1/2`, and the exact one-copy product cost
`3 ≤ 2 * 2` yields `2^(1*1*2) ≤ 2^(2*2)`. -/
noncomputable def exampleRate :
    ScaledDyadicRateLower ((3 : ℚ) / 2) 1 2 where
  steps := 1
  exponent := 1
  ratioNonnegative := by norm_num
  powerLower := by norm_num
  scaledExponent := by norm_num

example : 2 ^ (1 * 1 * 2 ^ exampleRate.steps) ≤
    2 ^ (2 * 2 ^ exampleRate.steps) := by
  exact exampleRate.nat_state_power_lower (safe := 3) (flat := 2)
    (stateCount := 2) (multiplicity := 1) (by norm_num) (by norm_num)

end StructuralExhaustion.Examples.FixedPointRepeatedSquareLower
