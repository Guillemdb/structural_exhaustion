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

/-! ## Exact natural-number transports -/

/-- Eliminate a fixed-width occupied part from an error-bearing scaled density
estimate. No finite universe is inspected. -/
theorem nat_remainder_density_with_error
    {rate remainderRate width skeleton mass remainder scale error : Nat}
    (rateSplit : rate = remainderRate + width * skeleton)
    (density : rate * mass * scale ≤
      skeleton * (width * mass + remainder) * scale + error) :
    remainderRate * mass * scale ≤
      skeleton * remainder * scale + error := by
  have cancel :
      remainderRate * mass * scale + width * skeleton * mass * scale ≤
        (skeleton * remainder * scale + error) +
          width * skeleton * mass * scale := by
    calc
      remainderRate * mass * scale + width * skeleton * mass * scale =
          rate * mass * scale := by rw [rateSplit]; ring
      _ ≤ skeleton * (width * mass + remainder) * scale + error := density
      _ = (skeleton * remainder * scale + error) +
          width * skeleton * mass * scale := by ring
  omega

/-- Partition-aware form of `nat_remainder_density_with_error`.  Keeping the
order partition as a separate input prevents applications from rewriting
inside unrelated order-dependent scale factors such as logarithms. -/
theorem nat_partition_density_with_error
    {rate remainderRate width skeleton mass remainder order scale error : Nat}
    (rateSplit : rate = remainderRate + width * skeleton)
    (partition : remainder + width * mass = order)
    (density : rate * mass * scale ≤ skeleton * order * scale + error) :
    remainderRate * mass * scale ≤
      skeleton * remainder * scale + error := by
  apply nat_remainder_density_with_error rateSplit
  calc
    rate * mass * scale ≤ skeleton * order * scale + error := density
    _ = skeleton * (width * mass + remainder) * scale + error := by
      rw [← partition]
      ring

/-- Combine a scaled density cap with a local wedge/supply ledger while
retaining the density error. The rate identities are explicit inputs, so
applications never normalize large concrete products. -/
theorem nat_scaled_wedge_with_error
    {baseline remainderRate wedgeRate incidence skeleton packing remainder
      wedgeCount surplusFactor surplus scale error : Nat}
    (wedgeRateSplit :
      baseline * remainderRate = wedgeRate + incidence * skeleton)
    (density : remainderRate * packing * scale ≤
      skeleton * remainder * scale + error)
    (wedgeFloor : baseline * remainder ≤
      wedgeCount + incidence * packing + surplusFactor * surplus) :
    wedgeRate * remainder * scale ≤
      remainderRate * wedgeCount * scale + incidence * error +
        surplusFactor * remainderRate * surplus * scale := by
  have scaledWedge :
      baseline * remainderRate * remainder * scale ≤
        remainderRate * wedgeCount * scale +
          incidence * remainderRate * packing * scale +
          surplusFactor * remainderRate * surplus * scale := by
    calc
      baseline * remainderRate * remainder * scale =
          (remainderRate * scale) * (baseline * remainder) := by ring
      _ ≤ (remainderRate * scale) *
          (wedgeCount + incidence * packing + surplusFactor * surplus) :=
        Nat.mul_le_mul_left _ wedgeFloor
      _ = remainderRate * wedgeCount * scale +
          incidence * remainderRate * packing * scale +
          surplusFactor * remainderRate * surplus * scale := by ring
  have scaledDensity :
      incidence * remainderRate * packing * scale ≤
        incidence * skeleton * remainder * scale + incidence * error := by
    calc
      incidence * remainderRate * packing * scale =
          incidence * (remainderRate * packing * scale) := by ring
      _ ≤ incidence * (skeleton * remainder * scale + error) :=
        Nat.mul_le_mul_left _ density
      _ = incidence * skeleton * remainder * scale + incidence * error := by ring
  have cancel :
      wedgeRate * remainder * scale +
          incidence * skeleton * remainder * scale ≤
        (remainderRate * wedgeCount * scale + incidence * error +
          surplusFactor * remainderRate * surplus * scale) +
            incidence * skeleton * remainder * scale := by
    calc
      wedgeRate * remainder * scale +
          incidence * skeleton * remainder * scale =
        baseline * remainderRate * remainder * scale := by
          rw [wedgeRateSplit]
          ring
      _ ≤ remainderRate * wedgeCount * scale +
          incidence * remainderRate * packing * scale +
          surplusFactor * remainderRate * surplus * scale := scaledWedge
      _ ≤ remainderRate * wedgeCount * scale +
          (incidence * skeleton * remainder * scale + incidence * error) +
          surplusFactor * remainderRate * surplus * scale :=
        Nat.add_le_add_right (Nat.add_le_add_left scaledDensity _) _
      _ = (remainderRate * wedgeCount * scale + incidence * error +
          surplusFactor * remainderRate * surplus * scale) +
            incidence * skeleton * remainder * scale := by ring
  omega

/-! ## Positive-scale normalization -/

/-- Divide an additive-error inequality by one positive common scale.  This
is purely ordered-field plumbing; applications retain their semantic terms as
opaque real values. -/
theorem scaled_le_main_add_error_div
    {left main exactError surplus scale : ℝ}
    (scalePositive : 0 < scale)
    (scaled : left * scale ≤
      main * scale + exactError + surplus * scale) :
    left ≤ main + exactError / scale + surplus := by
  have errorIdentity : exactError = (exactError / scale) * scale := by
    field_simp [ne_of_gt scalePositive]
  by_contra notLe
  have differencePositive :
      0 < left - (main + exactError / scale + surplus) :=
    sub_pos.mpr (lt_of_not_ge notLe)
  have scaledDifferencePositive := mul_pos differencePositive scalePositive
  nlinarith

/-- If `remainder` retains a fixed positive fraction of `order`, an error
which is little-o after division by `order` is also little-o after division by
`remainder`.  This theorem inspects no family members. -/
theorem tendsto_error_div_remainder_of_lower_density
    {ι : Type*} {l : Filter ι}
    (error remainder order : ι → ℝ) (densityConstant : ℝ)
    (densityConstantPositive : 0 < densityConstant)
    (errorNonnegative : ∀ᶠ i in l, 0 ≤ error i)
    (orderPositive : ∀ᶠ i in l, 0 < order i)
    (lowerDensity : ∀ᶠ i in l,
      densityConstant * order i ≤ remainder i)
    (normalizedZero : Tendsto (fun i => error i / order i) l (nhds 0)) :
    Tendsto (fun i => error i / remainder i) l (nhds 0) := by
  have upperZero : Tendsto
      (fun i => (1 / densityConstant) * (error i / order i))
      l (nhds 0) := by
    simpa using tendsto_const_nhds.mul normalizedZero
  refine squeeze_zero'
    (g := fun i => (1 / densityConstant) * (error i / order i)) ?_ ?_ upperZero
  · filter_upwards [errorNonnegative, orderPositive, lowerDensity]
      with i errorNonnegativeI orderPositiveI lowerDensityI
    exact div_nonneg errorNonnegativeI
      (le_trans (mul_nonneg densityConstantPositive.le orderPositiveI.le)
        lowerDensityI)
  · filter_upwards [errorNonnegative, orderPositive, lowerDensity]
      with i errorNonnegativeI orderPositiveI lowerDensityI
    have remainderPositive : 0 < remainder i :=
      lt_of_lt_of_le (mul_pos densityConstantPositive orderPositiveI)
        lowerDensityI
    rw [div_le_iff₀ remainderPositive]
    have upperNonnegative :
        0 ≤ (1 / densityConstant) * (error i / order i) :=
      mul_nonneg (by positivity) (div_nonneg errorNonnegativeI orderPositiveI.le)
    have scaledDensity :=
      mul_le_mul_of_nonneg_left lowerDensityI upperNonnegative
    have identity :
        (1 / densityConstant) * (error i / order i) *
            (densityConstant * order i) = error i := by
      field_simp [ne_of_gt densityConstantPositive, ne_of_gt orderPositiveI]
    nlinarith

end StructuralExhaustion.Core.DensityAsymptoticTransport
