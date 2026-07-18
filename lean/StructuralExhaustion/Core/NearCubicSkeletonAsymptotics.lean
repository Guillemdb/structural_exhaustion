import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import StructuralExhaustion.Core.DiscreteLinearLittleO

namespace StructuralExhaustion.Core.NearCubicSkeletonAsymptotics

/-- A concrete logarithmic upper bound for the labelled near-cubic skeleton
family.  The additive envelope is deliberately generous and linear; the
leading coefficient remains exactly `3/2`. -/
theorem log_choose_edgeSlots_edgeCount_le (n : Nat) (hn : 5 ≤ n) :
    Real.log ((Nat.choose (Nat.choose n 2) ((3 * n + 1) / 2) : Nat) : ℝ) ≤
      (3 / 2 : ℝ) * n * Real.log n + 3 * n + Real.log n + 1 := by
  let slots := Nat.choose n 2
  let edges := (3 * n + 1) / 2
  have npos : 0 < n := by omega
  have edgesPos : 0 < edges := by dsimp [edges]; omega
  have edgesLeSlots : edges ≤ slots := by
    dsimp [edges, slots]
    rw [Nat.choose_two_right]
    apply Nat.div_le_div_right
    calc
      3 * n + 1 ≤ 4 * n := by omega
      _ ≤ n * (n - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (show 4 ≤ n - 1 by omega)
  have slotsPos : 0 < slots := lt_of_lt_of_le edgesPos edgesLeSlots
  have choosePos : 0 < Nat.choose slots edges := Nat.choose_pos edgesLeSlots
  have chooseBound :
      ((Nat.choose slots edges : Nat) : ℝ) ≤
        (slots : ℝ) ^ edges / (edges.factorial : ℝ) :=
    Nat.choose_le_pow_div edges slots
  have factorialLogLower :
      (edges : ℝ) * Real.log edges - edges ≤
        Real.log (edges.factorial : ℝ) := by
    have stirling := Stirling.le_log_factorial_stirling edgesPos.ne'
    have logEdgesNonnegative : 0 ≤ Real.log edges :=
      Real.log_nonneg (by exact_mod_cast edgesPos)
    have logTwoPiNonnegative : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by have := Real.two_le_pi; nlinarith)
    linarith
  have quotientPos : 0 < (slots : ℝ) ^ edges / (edges.factorial : ℝ) := by
    positivity
  have logged := Real.log_le_log (by exact_mod_cast choosePos) chooseBound
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at logged
  have firstBound :
      Real.log ((Nat.choose slots edges : Nat) : ℝ) ≤
        (edges : ℝ) * (Real.log slots - Real.log edges + 1) := by
    linarith
  have edgesGeN : n ≤ edges := by dsimp [edges]; omega
  have slotsLe : slots ≤ n * edges := by
    calc
      slots = n * (n - 1) / 2 := by simp [slots, Nat.choose_two_right]
      _ ≤ n * (n - 1) := Nat.div_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      _ ≤ n * edges := Nat.mul_le_mul_left n edgesGeN
  have logSlotsLe : Real.log slots ≤ Real.log n + Real.log edges := by
    calc
      Real.log slots ≤ Real.log ((n : Nat) * edges) :=
        Real.log_le_log (by exact_mod_cast slotsPos) (by exact_mod_cast slotsLe)
      _ = Real.log n + Real.log edges := by
        rw [Real.log_mul (by exact_mod_cast npos.ne')
          (by exact_mod_cast edgesPos.ne')]
  have bracket : Real.log slots - Real.log edges + 1 ≤ Real.log n + 1 := by
    linarith
  have edgesCastBound : (edges : ℝ) ≤ (3 / 2 : ℝ) * n + 1 := by
    dsimp [edges]
    have : (edges : ℝ) ≤ ((3 * n + 1 : Nat) : ℝ) / 2 := by
      exact Nat.cast_div_le
    norm_num at this ⊢
    nlinarith
  have logNNonnegative : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast npos)
  calc
    _ ≤ (edges : ℝ) * (Real.log slots - Real.log edges + 1) := firstBound
    _ ≤ (edges : ℝ) * (Real.log n + 1) :=
      mul_le_mul_of_nonneg_left bracket (by positivity)
    _ ≤ ((3 / 2 : ℝ) * n + 1) * (Real.log n + 1) :=
      mul_le_mul_of_nonneg_right edgesCastBound (by positivity)
    _ ≤ (3 / 2 : ℝ) * n * Real.log n + 3 * n + Real.log n + 1 := by
      nlinarith

/-- The explicit correction in `log_choose_edgeSlots_edgeCount_le` is
little-o of `n log n`. -/
theorem skeletonErrorEnvelope_isLittleO :
    (fun n : Nat => (3 : ℝ) * n + Real.log (n : ℝ) + 1) =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  apply DiscreteLinearLittleO.isLittleO_natCast_mul_log_of_eventually_le_linear
    _ 4 (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have logarithm := Real.log_le_sub_one_of_pos npos
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

end StructuralExhaustion.Core.NearCubicSkeletonAsymptotics
