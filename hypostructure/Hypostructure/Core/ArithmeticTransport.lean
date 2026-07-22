import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Hypostructure.Core.ArithmeticTransport

/-! Generic arithmetic used by finite density, entropy, and budget nodes.
The inputs are certificates owned by the predecessor; this module never
constructs a problem-specific family or chooses a numerical constant. -/

theorem complement_lower
    {rate complement width budget mass remainder order : Nat}
    (rate_split : rate = complement + width * budget)
    (partition : remainder + width * mass = order)
    (density : rate * mass ≤ budget * order) :
    complement * order ≤ rate * remainder := by
  have scaled := Nat.mul_le_mul_left width density
  have common : complement * order + width * (budget * order) ≤
      rate * remainder + width * (budget * order) := by
    calc
      complement * order + width * (budget * order) = rate * order := by
        rw [rate_split]
        ring
      _ = rate * remainder + width * (rate * mass) := by
        rw [← partition]
        ring
      _ ≤ rate * remainder + width * (budget * order) := by
        exact Nat.add_le_add_left scaled _
  exact Nat.le_of_add_le_add_right common

structure PoweredCapacity where
  stateCount : Nat
  base : Nat
  exponent : Nat
  paidExponent : Nat
  desiredExponent : Nat
  errorExponent : Nat
  capacity : Nat
  paid : stateCount ^ exponent * base ^ paidExponent ≤ capacity ^ exponent
  desired_eq : desiredExponent = paidExponent + errorExponent

theorem PoweredCapacity.with_error (profile : PoweredCapacity) :
    profile.stateCount ^ profile.exponent * profile.base ^ profile.desiredExponent ≤
      profile.capacity ^ profile.exponent * profile.base ^ profile.errorExponent := by
  rw [profile.desired_eq, pow_add]
  calc
    profile.stateCount ^ profile.exponent *
        (profile.base ^ profile.paidExponent * profile.base ^ profile.errorExponent) =
        (profile.stateCount ^ profile.exponent * profile.base ^ profile.paidExponent) *
          profile.base ^ profile.errorExponent := by ring
    _ ≤ profile.capacity ^ profile.exponent * profile.base ^ profile.errorExponent :=
      Nat.mul_le_mul_right _ profile.paid

theorem PoweredCapacity.logb_with_error (profile : PoweredCapacity)
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
    exact_mod_cast profile.with_error
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

structure ErrorWithinGap (main threshold scale error : ℝ) : Prop where
  error_lt : error < (threshold - main) * scale

theorem normalized_lt_threshold
    {quantity scale error main threshold : ℝ}
    (scale_pos : 0 < scale)
    (cap : quantity ≤ main * scale + error)
    (small : ErrorWithinGap main threshold scale error) :
    quantity / scale < threshold := by
  have strict : quantity < threshold * scale := by
    calc
      quantity ≤ main * scale + error := cap
      _ < main * scale + (threshold - main) * scale := by
        nlinarith [small.error_lt]
      _ = threshold * scale := by ring
  exact (div_lt_iff₀ scale_pos).mpr strict

/-! ## Error-bearing density transports -/

theorem nat_partition_density_with_error
    {rate remainderRate width skeleton mass remainder order scale error : Nat}
    (rateSplit : rate = remainderRate + width * skeleton)
    (partition : remainder + width * mass = order)
    (density : rate * mass * scale ≤ skeleton * order * scale + error) :
    remainderRate * mass * scale ≤
      skeleton * remainder * scale + error := by
  have cancel :
      remainderRate * mass * scale + width * skeleton * mass * scale ≤
        (skeleton * remainder * scale + error) +
          width * skeleton * mass * scale := by
    calc
      remainderRate * mass * scale + width * skeleton * mass * scale =
          rate * mass * scale := by rw [rateSplit]; ring
      _ ≤ skeleton * order * scale + error := density
      _ = skeleton * (width * mass + remainder) * scale + error := by
        rw [← partition]
        ring
      _ = (skeleton * remainder * scale + error) +
          width * skeleton * mass * scale := by ring
  omega

theorem nat_partition_complement_lower
    {rate complementRate width budget mass remainder order : Nat}
    (rateSplit : rate = complementRate + width * budget)
    (partition : remainder + width * mass = order)
    (density : rate * mass ≤ budget * order) :
    complementRate * order ≤ rate * remainder := by
  have scaledDensity :
      width * (rate * mass) ≤ width * (budget * order) :=
    Nat.mul_le_mul_left width density
  have withCommonTerm :
      complementRate * order + width * (budget * order) ≤
        rate * remainder + width * (budget * order) := by
    calc
      complementRate * order + width * (budget * order) =
          rate * order := by rw [rateSplit]; ring
      _ = rate * remainder + width * (rate * mass) := by
        rw [← partition]
        ring
      _ ≤ rate * remainder + width * (budget * order) :=
        Nat.add_le_add_left scaledDensity _
  exact Nat.le_of_add_le_add_right withCommonTerm

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

/-! ## Powered-budget and strict-gap transports -/

namespace PoweredTransfer

structure Profile where
  forced : Nat
  flat : Nat
  stateCount : Nat
  upper : Nat
  scale : Nat
  forced_le_flat_mul_stateCount : forced ≤ flat * stateCount
  stateCount_pow_lt_upper : stateCount ^ scale < upper
  flat_pos : 0 < flat

theorem forced_pow_lt_flat_pow_mul_upper (profile : Profile) :
    profile.forced ^ profile.scale <
      profile.flat ^ profile.scale * profile.upper := by
  have poweredStep : profile.forced ^ profile.scale ≤
      (profile.flat * profile.stateCount) ^ profile.scale :=
    Nat.pow_le_pow_left profile.forced_le_flat_mul_stateCount profile.scale
  rw [Nat.mul_pow] at poweredStep
  have flatPowerPos : 0 < profile.flat ^ profile.scale :=
    Nat.pow_pos profile.flat_pos
  have poweredUpper :
      profile.flat ^ profile.scale * profile.stateCount ^ profile.scale <
        profile.flat ^ profile.scale * profile.upper :=
    Nat.mul_lt_mul_of_pos_left profile.stateCount_pow_lt_upper flatPowerPos
  exact poweredStep.trans_lt poweredUpper

theorem forced_pow_lt_flat_pow_mul_upper_of
    {forced flat stateCount upper scale : Nat}
    (forcedLe : forced ≤ flat * stateCount)
    (statePowLt : stateCount ^ scale < upper)
    (flatPos : 0 < flat) :
    forced ^ scale < flat ^ scale * upper :=
  forced_pow_lt_flat_pow_mul_upper
    { forced := forced, flat := flat, stateCount := stateCount,
      upper := upper, scale := scale,
      forced_le_flat_mul_stateCount := forcedLe,
      stateCount_pow_lt_upper := statePowLt, flat_pos := flatPos }

end PoweredTransfer

namespace StrictGap

structure ErrorWithinGap (main threshold scale error : ℝ) : Prop where
  error_lt_gap_mul_scale : error < (threshold - main) * scale

structure TailSmallError (main threshold scale error : ℝ) : Prop where
  gap_pos : 0 < threshold - main

structure LargeEnoughTail : Prop where
  withinGap : ∀ {main threshold scale error : ℝ},
    TailSmallError main threshold scale error →
      ErrorWithinGap main threshold scale error

theorem normalized_lt_threshold
    {quantity scale error main threshold : ℝ}
    (scale_pos : 0 < scale)
    (cap : quantity ≤ main * scale + error)
    (_gap : main < threshold)
    (small : ErrorWithinGap main threshold scale error) :
    quantity / scale < threshold := by
  have absorbed : quantity < threshold * scale := by
    calc
      quantity ≤ main * scale + error := cap
      _ < main * scale + (threshold - main) * scale := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_lt_add_left small.error_lt_gap_mul_scale (main * scale)
      _ = threshold * scale := by ring
  exact (div_lt_iff₀ scale_pos).mpr absorbed

theorem denom_mul_lt_of_normalized_lt_inv
    {denom quantity scale : Nat}
    (denom_pos : 0 < denom)
    (scale_pos : 0 < scale)
    (strict : (quantity : ℝ) / (scale : ℝ) <
      (1 / (denom : ℝ) : ℝ)) :
    denom * quantity < scale := by
  have scale_pos_real : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have denom_pos_real : (0 : ℝ) < denom := by exact_mod_cast denom_pos
  rw [div_lt_iff₀ scale_pos_real] at strict
  have scaledReal : (denom : ℝ) * (quantity : ℝ) < (scale : ℝ) := by
    rw [one_div] at strict
    calc
      (denom : ℝ) * (quantity : ℝ) <
          (denom : ℝ) * ((denom : ℝ)⁻¹ * (scale : ℝ)) :=
        mul_lt_mul_of_pos_left strict denom_pos_real
      _ = (scale : ℝ) := by
        field_simp [ne_of_gt denom_pos_real]
  have scaled : ((denom * quantity : Nat) : ℝ) < (scale : ℝ) := by
    norm_num
    exact scaledReal
  exact_mod_cast scaled

theorem scaled_charge_negative_of_mul_lt
    {budget quantity scale : Nat}
    (strict : budget * quantity < scale) :
    (budget : Int) * (quantity : Int) - (scale : Int) < 0 := by
  omega

theorem quarter_charge_negative
    {quantity scale : Nat}
    (strict : 4 * quantity < scale) :
    4 * (quantity : Int) - (scale : Int) < 0 :=
  scaled_charge_negative_of_mul_lt strict

theorem signed_nonnegative_false_of_nat_sub_scaled_negative
    {budget a b scale : Nat}
    (negative :
      (budget : Int) * (((a - b : Nat) : Int)) - (scale : Int) < 0)
    (nonnegative :
      0 ≤ (budget : Int) * ((a : Int) - (b : Int)) - (scale : Int)) :
    False := by
  by_cases h : b ≤ a
  · have natSub_eq : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
      omega
    rw [natSub_eq] at negative
    omega
  · have intDiff_neg : (a : Int) - (b : Int) < 0 := by omega
    have natSub_zero : a - b = 0 := by
      exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)
    have scale_pos : (0 : Int) < (scale : Int) := by
      rw [natSub_zero] at negative
      simp at negative
      omega
    have scale_nonneg : (0 : Int) ≤ (scale : Int) := by
      exact_mod_cast scale.zero_le
    have budget_nonneg : (0 : Int) ≤ (budget : Int) := by
      exact_mod_cast budget.zero_le
    have product_nonpos :
        (budget : Int) * ((a : Int) - (b : Int)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos budget_nonneg intDiff_neg.le
    have charge_neg :
        (budget : Int) * ((a : Int) - (b : Int)) - (scale : Int) < 0 := by
      omega
    omega

end StrictGap

end Hypostructure.Core.ArithmeticTransport
