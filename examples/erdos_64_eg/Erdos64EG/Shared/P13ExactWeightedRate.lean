import Erdos64EG.Node21
import Erdos64EG.Shared.P13WeightedHotColdInterface
import StructuralExhaustion.Core.FixedPointRepeatedSquareLower

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.FixedPointRepeatedSquareLower

universe u

set_option maxRecDepth 100000

/-!
# Exact fixed-point certificate for the P13 weighted rate

This file certifies the manuscript's rational lower rate
`118108581006 / 10^9` directly from the exact node-[21] safe and flat
products.  It checks 34 bounded repeated-square rows.  It does not evaluate
the equivalent multi-billion-bit power inequality and uses no floating point
or real logarithm.
-/

def p13ExactWeightedRateDenominator : Nat := 10 ^ 40

def p13ExactWeightedRateInitialLower : Nat :=
  10781672600910877398201228224441972344885

def p13ExactWeightedRateShifts : List Nat :=
  [0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]

def p13ExactWeightedRateRun :
    Run p13ExactWeightedRateDenominator p13ExactWeightedRateInitialLower 118 :=
  Run.ofShifts p13ExactWeightedRateDenominator
    p13ExactWeightedRateInitialLower 118 p13ExactWeightedRateShifts

theorem p13ExactWeightedRate_initial_cross :
    (2 ^ 118 * p13BarrierFlatProduct) * p13ExactWeightedRateInitialLower ≤
      p13BarrierSafeProduct * p13ExactWeightedRateDenominator := by
  native_decide

theorem p13ExactWeightedRate_steps : p13ExactWeightedRateRun.steps = 34 := by
  native_decide

theorem p13ExactWeightedRate_finalExponent :
    p13ExactWeightedRateRun.finalExponent = 2029089971192 := by
  native_decide

theorem p13ExactWeightedRate_finalLower :
    p13ExactWeightedRateDenominator ≤ p13ExactWeightedRateRun.finalLower := by
  native_decide

theorem p13ExactWeightedRate_scaledExponent :
    118108581006 * 2 ^ p13ExactWeightedRateRun.steps ≤
      1000000000 * p13ExactWeightedRateRun.finalExponent := by
  native_decide

private theorem p13ExactWeightedRate_initial_rational :
    (2 : ℚ) ^ 118 * (p13ExactWeightedRateInitialLower : ℚ) /
        p13ExactWeightedRateDenominator ≤
      (p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct := by
  have denominatorPositive : (0 : ℚ) < p13ExactWeightedRateDenominator := by
    norm_num [p13ExactWeightedRateDenominator]
  have flatPositive : (0 : ℚ) < p13BarrierFlatProduct := by
    have : 0 < p13BarrierFlatProduct := by native_decide
    exact_mod_cast this
  apply (div_le_div_iff₀ denominatorPositive flatPositive).2
  exact_mod_cast p13ExactWeightedRate_initial_cross

/-- Kernel-checked exact lower-rate certificate for the printed node-[24]
constant.  Its power field is obtained by the generic fixed-point soundness
theorem, not by normalizing a gigantic power. -/
noncomputable def p13ExactWeightedRateCertificate :
    ScaledDyadicRateLower
      ((p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct)
      118108581006 1000000000 := by
  let ratio : ℚ := (p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct
  have ratioNonnegative : 0 ≤ ratio := by positivity
  have sound := p13ExactWeightedRateRun.sound
    (by norm_num [p13ExactWeightedRateDenominator]) ratio ratioNonnegative
      p13ExactWeightedRate_initial_rational
  have denominatorPositive : (0 : ℚ) < p13ExactWeightedRateDenominator := by
    norm_num [p13ExactWeightedRateDenominator]
  have finalFactor :
      (1 : ℚ) ≤ (p13ExactWeightedRateRun.finalLower : ℚ) /
        p13ExactWeightedRateDenominator := by
    apply (le_div_iff₀ denominatorPositive).2
    exact_mod_cast p13ExactWeightedRate_finalLower
  refine {
    steps := p13ExactWeightedRateRun.steps
    exponent := p13ExactWeightedRateRun.finalExponent
    ratioNonnegative := ratioNonnegative
    powerLower := ?_
    scaledExponent := p13ExactWeightedRate_scaledExponent
  }
  calc
    (2 : ℚ) ^ p13ExactWeightedRateRun.finalExponent =
        (2 : ℚ) ^ p13ExactWeightedRateRun.finalExponent * 1 := by ring
    _ ≤ (2 : ℚ) ^ p13ExactWeightedRateRun.finalExponent *
          ((p13ExactWeightedRateRun.finalLower : ℚ) /
            p13ExactWeightedRateDenominator) := by
      exact mul_le_mul_of_nonneg_left finalFactor (by positivity)
    _ = (2 : ℚ) ^ p13ExactWeightedRateRun.finalExponent *
          (p13ExactWeightedRateRun.finalLower : ℚ) /
            p13ExactWeightedRateDenominator := by ring
    _ ≤ ratio ^ (2 ^ p13ExactWeightedRateRun.steps) := sound

/-- One exact graph-owned weighted package pays the printed rational rate in
powered integer form.  This is the rounding-free strengthening of the older
118-bit floor: it consumes the package's conditional-fibre telescope and the
bounded repeated-square certificate, and enumerates no state product. -/
theorem P13WeightedLiveWindowPackage.exactStatePowerLower
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    2 ^ (118108581006 * package.scaleMultiplicity *
        2 ^ p13ExactWeightedRateCertificate.steps) ≤
      package.states.values.length ^
        (1000000000 * 2 ^ p13ExactWeightedRateCertificate.steps) := by
  have powered := p13ExactWeightedRateCertificate.nat_state_power_lower
    (flatPositive := p13Sequential_flatProduct_pos)
    (by simpa [package.safeProductExact, package.flatProductExact] using
      package.product_le)
  rw [package.profileExact] at powered
  exact powered

end Erdos64EG.Internal
