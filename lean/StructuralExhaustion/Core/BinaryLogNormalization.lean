import StructuralExhaustion.Core.DiscreteLinearLittleO

namespace StructuralExhaustion.Core.BinaryLogNormalization

open Filter Asymptotics

/-- The binary floor logarithm, converted back to natural logarithmic units,
never exceeds the natural logarithm. -/
theorem natLog_two_mul_realLog_le (n : Nat) (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have powerBound := Nat.pow_log_le_self 2 hn
  have powerBoundReal :
      ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast powerBound
  have logged := Real.log_le_log (by positivity : (0 : ℝ) <
      (2 : ℝ) ^ Nat.log 2 n) powerBoundReal
  simpa [Real.log_pow] using logged

/-- Rounding `log₂ n` down loses at most one binary digit.  This is the
uniform bridge between exact `Nat.log` accounting and real-log asymptotics. -/
theorem realLog_sub_natLog_two_mul_le (n : Nat) (hn : n ≠ 0) :
    Real.log n - (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log 2 := by
  have strictPower := Nat.lt_pow_succ_log_self (show 1 < 2 by omega) n
  have strictPowerReal :
      (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n).succ := by
    exact_mod_cast strictPower
  have nposReal : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have powerPosReal : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 n).succ := by
    positivity
  have logged := Real.strictMonoOn_log
    nposReal powerPosReal
    strictPowerReal
  rw [Real.log_pow] at logged
  push_cast at logged
  nlinarith

/-- If an exact natural bit count `powered` has the usual real-log upper
bound and `printed` is exactly its floor-log main term, then natural
subtraction contributes only the supplied error plus one binary digit per
unit of the leading coefficient. -/
theorem natSub_cast_le_roundingEnvelope
    (powered printed n : Nat) (leading error : ℝ)
    (hn : n ≠ 0) (hleading : 0 ≤ leading) (herror : 0 ≤ error)
    (poweredUpper :
      (powered : ℝ) * Real.log 2 ≤
        leading * (n : ℝ) * Real.log n + error)
    (printedExact :
      (printed : ℝ) * Real.log 2 =
        leading * (n : ℝ) *
          ((Nat.log 2 n : ℝ) * Real.log 2)) :
    ((powered - printed : Nat) : ℝ) ≤
      error / Real.log 2 + leading * n := by
  have logTwoPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have rounding := realLog_sub_natLog_two_mul_le n hn
  by_cases hprinted : printed ≤ powered
  · rw [Nat.cast_sub hprinted]
    have scaledRounding :
        leading * (n : ℝ) *
            (Real.log n - (Nat.log 2 n : ℝ) * Real.log 2) ≤
          leading * (n : ℝ) * Real.log 2 := by
      exact mul_le_mul_of_nonneg_left rounding (mul_nonneg hleading (by positivity))
    have multiplied :
        ((powered : ℝ) - printed) * Real.log 2 ≤
          error + leading * n * Real.log 2 := by
      rw [sub_mul, printedExact]
      nlinarith [poweredUpper, scaledRounding]
    calc
      (powered : ℝ) - printed ≤
          (error + leading * n * Real.log 2) / Real.log 2 :=
        (le_div_iff₀ logTwoPos).2 multiplied
      _ = error / Real.log 2 + leading * n := by
        field_simp
  · have subtractionZero : powered - printed = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hprinted)
    rw [subtractionZero]
    norm_num
    exact add_nonneg (div_nonneg herror logTwoPos.le)
      (mul_nonneg hleading (Nat.cast_nonneg n))

/-- The combined rounding envelope remains little-o of `n log n` whenever
its pre-existing error term is little-o. -/
theorem roundingEnvelope_isLittleO
    (error : Nat → ℝ)
    (errorLittleO : error =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)))
    (leading : ℝ) :
    (fun n : Nat => error n / Real.log 2 + leading * n) =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have divided := errorLittleO.const_mul_left (Real.log 2)⁻¹
  have linear :=
    DiscreteLinearLittleO.const_mul_natCast_isLittleO_natCast_mul_log leading
  simpa [div_eq_mul_inv, mul_comm] using divided.add linear

/-- Replacing the real logarithm in the normalizing denominator by the exact
binary floor logarithm preserves convergence of a little-o error to zero.
This is the reusable discrete normalization step used by finite bit ledgers. -/
theorem tendsto_div_natCast_mul_natLog_two_nhds_zero
    (error : Nat → ℝ)
    (errorLittleO : error =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ))) :
    Filter.Tendsto
      (fun n : Nat => error n / ((n : ℝ) * (Nat.log 2 n : ℝ)))
      atTop (nhds 0) := by
  let realDenominator := fun n : Nat => (n : ℝ) * Real.log (n : ℝ)
  let discreteDenominator := fun n : Nat => (n : ℝ) * (Nat.log 2 n : ℝ)
  have denominatorBigO : realDenominator =O[atTop] discreteDenominator := by
    have logTwoPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have withConstant : IsBigOWith (2 * Real.log 2) atTop
        realDenominator discreteDenominator := by
      apply isBigOWith_iff.2
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have nNonzero : n ≠ 0 := by omega
      have logFloorPositive : 0 < Nat.log 2 n :=
        Nat.log_pos (show 1 < 2 by omega) hn
      have rounding := realLog_sub_natLog_two_mul_le n nNonzero
      have logBound :
          Real.log (n : ℝ) ≤ 2 * Real.log 2 * (Nat.log 2 n : ℝ) := by
        have oneLeFloor : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast logFloorPositive
        nlinarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n)
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))),
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))]
      dsimp [realDenominator, discreteDenominator]
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    exact withConstant.isBigO
  have discreteLittleO : error =o[atTop] discreteDenominator :=
    errorLittleO.trans_isBigO denominatorBigO
  simpa [discreteDenominator] using discreteLittleO.tendsto_div_nhds_zero

/-- Division bridge for a finite cross-multiplied bit budget.  Keeping this
elementary field calculation generic prevents concrete graph structures from
being unfolded during normalization. -/
theorem ratio_le_main_add_normalizedError
    (mass order rate main logScale certificateScale exactError envelope : ℝ)
    (orderPositive : 0 < order) (ratePositive : 0 < rate)
    (logScalePositive : 0 < logScale)
    (certificateScalePositive : 0 < certificateScale)
    (finiteCap :
      rate * mass * logScale * certificateScale ≤
        main * order * logScale * certificateScale + exactError)
    (errorBound : exactError ≤ envelope) :
    mass / order ≤
      main / rate +
        (1 / (rate * certificateScale)) *
          (envelope / (order * logScale)) := by
  field_simp
  nlinarith

end StructuralExhaustion.Core.BinaryLogNormalization
