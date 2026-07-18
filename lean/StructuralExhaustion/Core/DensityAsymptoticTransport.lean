import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StructuralExhaustion.Core.DensityAsymptoticTransport

open Filter

/-!
Reusable real-arithmetic transport for an error-bearing density estimate.
The first theorem sends a density upper bound through an exact
order/remainder partition.  The second sends it through the increasing
fractional-linear map `x |-> scale*x/(1-width*x)`.  No finite universe is
inspected by either operation.
-/

/-- An exact partition `remainder + width * mass = order` turns an additive
density error into the corresponding additive remainder error. -/
theorem remainder_ratio_lower
    {order mass remainder main error width : ℝ}
    (orderPositive : 0 < order)
    (widthNonnegative : 0 ≤ width)
    (partition : remainder + width * mass = order)
    (density : mass / order ≤ main + error) :
    1 - width * main - width * error ≤ remainder / order := by
  rw [div_le_iff₀ orderPositive] at density
  rw [le_div_iff₀ orderPositive]
  have scaledDensity :
      width * mass ≤ width * ((main + error) * order) :=
    mul_le_mul_of_nonneg_left density widthNonnegative
  ring_nf at scaledDensity ⊢
  linarith

/-- Multiplying a vanishing additive density error by a fixed width again
gives a vanishing error. -/
theorem remainder_error_tendsto_zero
    {ι : Type*} {l : Filter ι} (width : ℝ) {error : ι → ℝ}
    (errorZero : Tendsto error l (nhds 0)) :
    Tendsto (fun i => width * error i) l (nhds 0) := by
  simpa using tendsto_const_nhds.mul errorZero

/-- Exact correction when the fractional-linear input increases from `main`
to `main + error`. -/
noncomputable def fractionalLinearError
    (scale width main error : ℝ) : ℝ :=
  scale * (main + error) / (1 - width * (main + error)) -
    scale * main / (1 - width * main)

/-- The fractional-linear correction vanishes with its input error whenever
the limiting denominator is nonzero. -/
theorem fractionalLinearError_tendsto_zero
    {ι : Type*} {l : Filter ι} (scale width main : ℝ) {error : ι → ℝ}
    (errorZero : Tendsto error l (nhds 0))
    (denominatorNonzero : 1 - width * main ≠ 0) :
    Tendsto (fun i => fractionalLinearError scale width main (error i))
      l (nhds 0) := by
  have shifted : Tendsto (fun i => main + error i) l (nhds main) := by
    simpa using tendsto_const_nhds.add errorZero
  have secondDenominator :
      Tendsto (fun i => 1 - width * (main + error i)) l
        (nhds (1 - width * main)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul shifted)
  have numerator : Tendsto (fun i => scale * (main + error i)) l
      (nhds (scale * main)) := by
    simpa using tendsto_const_nhds.mul shifted
  have quotient := numerator.div secondDenominator denominatorNonzero
  simpa [fractionalLinearError] using
    quotient.sub (tendsto_const_nhds :
      Tendsto (fun _ : ι => scale * main / (1 - width * main)) l
        (nhds (scale * main / (1 - width * main))))

/-- Monotonicity plus the exact correction identity transports an additive
density error through the fractional-linear map. -/
theorem fractionalLinear_le_add_error
    {scale width main error value : ℝ}
    (scaleNonnegative : 0 ≤ scale)
    (widthNonnegative : 0 ≤ width)
    (_valueNonnegative : 0 ≤ value)
    (density : value ≤ main + error)
    (_mainDenominatorPositive : 0 < 1 - width * main)
    (errorDenominatorPositive : 0 < 1 - width * (main + error)) :
    scale * value / (1 - width * value) ≤
      scale * main / (1 - width * main) +
        fractionalLinearError scale width main error := by
  have valueDenominatorPositive : 0 < 1 - width * value := by
    nlinarith [mul_le_mul_of_nonneg_left density widthNonnegative]
  have monotoneStep :
      scale * value / (1 - width * value) ≤
        scale * (main + error) / (1 - width * (main + error)) := by
    rw [div_le_div_iff₀ valueDenominatorPositive errorDenominatorPositive]
    nlinarith [mul_nonneg scaleNonnegative
      (sub_nonneg.mpr density)]
  have correctionIdentity :
      scale * (main + error) / (1 - width * (main + error)) =
        scale * main / (1 - width * main) +
          fractionalLinearError scale width main error := by
    unfold fractionalLinearError
    ring
  exact monotoneStep.trans_eq correctionIdentity

end StructuralExhaustion.Core.DensityAsymptoticTransport
