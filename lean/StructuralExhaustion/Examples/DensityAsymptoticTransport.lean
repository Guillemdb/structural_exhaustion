import StructuralExhaustion.Core.DensityAsymptoticTransport

namespace StructuralExhaustion.Examples.DensityAsymptoticTransport

open Filter
open StructuralExhaustion.Core.DensityAsymptoticTransport

/-! A target-independent arithmetic fixture for the reusable transports. -/

example {order mass remainder : ℝ} (orderPositive : 0 < order)
    (partition : remainder + 2 * mass = order)
    (density : mass / order ≤ (1 : ℝ) / 5 + 1 / 100) :
    1 - 2 * ((1 : ℝ) / 5) - 2 * (1 / 100) ≤ remainder / order :=
  remainder_ratio_lower orderPositive (by norm_num) partition density

example :
    Tendsto
      (fun n : Nat => fractionalLinearError 3 2 ((1 : ℝ) / 5)
        (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
  apply fractionalLinearError_tendsto_zero
  · have denominatorAtTop :
        Tendsto (fun n : Nat => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1)).div_atTop
        denominatorAtTop
  · norm_num

example {value error : ℝ} (valueNonnegative : 0 ≤ value)
    (density : value ≤ (1 : ℝ) / 5 + error)
    (errorSmall : error < 3 / 10) :
    3 * value / (1 - 2 * value) ≤
      3 * ((1 : ℝ) / 5) / (1 - 2 * ((1 : ℝ) / 5)) +
        fractionalLinearError 3 2 ((1 : ℝ) / 5) error := by
  apply fractionalLinear_le_add_error (by norm_num) (by norm_num)
    valueNonnegative density
  · norm_num
  · norm_num
    linarith

example {mass remainder scale error : Nat}
    (density : 11 * mass * scale ≤
      2 * (3 * mass + remainder) * scale + error) :
    5 * mass * scale ≤ 2 * remainder * scale + error :=
  nat_remainder_density_with_error (by norm_num) density

example {mass remainder order scale error : Nat}
    (partition : remainder + 3 * mass = order)
    (density : 11 * mass * scale ≤ 2 * order * scale + error) :
    5 * mass * scale ≤ 2 * remainder * scale + error :=
  nat_partition_density_with_error (by norm_num) partition density

example {packing remainder wedge surplus scale error : Nat}
    (density : 5 * packing * scale ≤
      2 * remainder * scale + error)
    (wedgeFloor : 3 * remainder ≤ wedge + 4 * packing + 2 * surplus) :
    7 * remainder * scale ≤
      5 * wedge * scale + 4 * error + 2 * 5 * surplus * scale :=
  nat_scaled_wedge_with_error (by norm_num) density wedgeFloor

example {left main error surplus scale : ℝ} (scalePositive : 0 < scale)
    (scaled : left * scale ≤ main * scale + error + surplus * scale) :
    left ≤ main + error / scale + surplus :=
  scaled_le_main_add_error_div scalePositive scaled

example {ι : Type*} {l : Filter ι}
    (error remainder order : ι → ℝ)
    (errorNonnegative : ∀ᶠ i in l, 0 ≤ error i)
    (orderPositive : ∀ᶠ i in l, 0 < order i)
    (quarterDensity : ∀ᶠ i in l, (1 / 4 : ℝ) * order i ≤ remainder i)
    (normalizedZero : Tendsto (fun i => error i / order i) l (nhds 0)) :
    Tendsto (fun i => error i / remainder i) l (nhds 0) :=
  tendsto_error_div_remainder_of_lower_density
    error remainder order (1 / 4) (by norm_num)
    errorNonnegative orderPositive quarterDensity normalizedZero

end StructuralExhaustion.Examples.DensityAsymptoticTransport
