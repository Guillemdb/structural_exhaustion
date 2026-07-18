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

end StructuralExhaustion.Examples.DensityAsymptoticTransport
