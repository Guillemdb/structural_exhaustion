import Mathlib

namespace StructuralExhaustion.Core.FixedPointRepeatedSquareLower

/-!
# Fixed-point repeated-square lower certificates

For a positive denominator `D`, a lower numerator `L`, and exponent ledger
`K`, the semantic invariant is

`2^K * (L / D) <= x`.

One certificate bit `q` replaces `x` by `x^2`, replaces `K` by `2*K+q`,
and replaces `L` by `floor (L^2 / (D*2^q))`.  The floor is deliberately a
lower rounding: `D*2^q*nextLower <= L^2`.  Iterating therefore proves a
lower dyadic exponent for a repeated square without materializing the large
power being bounded.
-/

/-- The downward-rounded numerator after one certified square. -/
def nextLower (denominator lower shift : Nat) : Nat :=
  lower ^ 2 / (denominator * 2 ^ shift)

/-- A proof-carrying fixed-point run.  Its final numerator, exponent, and
number of squares are computed recursively from the supplied shift word. -/
inductive Run (denominator : Nat) : Nat → Nat → Type where
  | stop (lower exponent : Nat) : Run denominator lower exponent
  | next (lower exponent shift : Nat)
      (tail : Run denominator
        (nextLower denominator lower shift) (2 * exponent + shift)) :
      Run denominator lower exponent

namespace Run

def finalLower {denominator lower exponent}
    (run : Run denominator lower exponent) : Nat :=
  match run with
  | .stop lower _ => lower
  | .next _ _ _ tail => tail.finalLower

def finalExponent {denominator lower exponent}
    (run : Run denominator lower exponent) : Nat :=
  match run with
  | .stop _ exponent => exponent
  | .next _ _ _ tail => tail.finalExponent

def steps {denominator lower exponent}
    (run : Run denominator lower exponent) : Nat :=
  match run with
  | .stop _ _ => 0
  | .next _ _ _ tail => tail.steps + 1

/-- Build the canonical run from an explicit finite shift word. -/
def ofShifts (denominator lower exponent : Nat) : List Nat →
    Run denominator lower exponent
  | [] => .stop lower exponent
  | shift :: shifts =>
      .next lower exponent shift
        (ofShifts denominator (nextLower denominator lower shift)
          (2 * exponent + shift) shifts)

theorem nextLower_mul_le (denominator lower shift : Nat) :
    denominator * 2 ^ shift * nextLower denominator lower shift ≤ lower ^ 2 := by
  simpa [nextLower, Nat.mul_assoc] using
    Nat.mul_div_le (lower ^ 2) (denominator * 2 ^ shift)

private theorem one_step
    (denominator lower exponent shift : Nat)
    (denominatorPositive : 0 < denominator)
    (x : ℚ)
    (xNonnegative : 0 ≤ x)
    (bound : (2 : ℚ) ^ exponent * (lower : ℚ) / denominator ≤ x) :
    (2 : ℚ) ^ (2 * exponent + shift) *
          (nextLower denominator lower shift : ℚ) / denominator ≤ x ^ 2 := by
  have denominatorPositiveQ : (0 : ℚ) < denominator := by exact_mod_cast denominatorPositive
  have roundedNat := nextLower_mul_le denominator lower shift
  have roundedQ :
      (denominator : ℚ) * (2 : ℚ) ^ shift *
          (nextLower denominator lower shift : ℚ) ≤ (lower : ℚ) ^ 2 := by
    exact_mod_cast roundedNat
  have fractionBound :
      (2 : ℚ) ^ shift * (nextLower denominator lower shift : ℚ) /
          denominator ≤ (lower : ℚ) ^ 2 / denominator ^ 2 := by
    apply (div_le_div_iff₀ denominatorPositiveQ
      (sq_pos_of_pos denominatorPositiveQ)).2
    nlinarith [roundedQ]
  have factorNonnegative : 0 ≤ (2 : ℚ) ^ (2 * exponent) := by positivity
  calc
    (2 : ℚ) ^ (2 * exponent + shift) *
          (nextLower denominator lower shift : ℚ) / denominator =
        (2 : ℚ) ^ (2 * exponent) *
          ((2 : ℚ) ^ shift *
            (nextLower denominator lower shift : ℚ) / denominator) := by
      rw [pow_add]
      ring
    _ ≤ (2 : ℚ) ^ (2 * exponent) *
          ((lower : ℚ) ^ 2 / denominator ^ 2) :=
      mul_le_mul_of_nonneg_left fractionBound factorNonnegative
    _ = ((2 : ℚ) ^ exponent * (lower : ℚ) / denominator) ^ 2 := by
      rw [show 2 * exponent = exponent + exponent by omega, pow_add]
      ring
    _ ≤ x ^ 2 := by
      have leftNonnegative :
          0 ≤ (2 : ℚ) ^ exponent * (lower : ℚ) / denominator := by positivity
      nlinarith

/-- Soundness of the bounded checker.  A run of `s` rows proves its final
fixed-point lower bound for `x^(2^s)`. -/
theorem sound
    {denominator lower exponent : Nat}
    (run : Run denominator lower exponent)
    (denominatorPositive : 0 < denominator)
    (x : ℚ)
    (xNonnegative : 0 ≤ x)
    (bound : (2 : ℚ) ^ exponent * (lower : ℚ) / denominator ≤ x) :
    (2 : ℚ) ^ run.finalExponent * (run.finalLower : ℚ) / denominator ≤
      x ^ (2 ^ run.steps) := by
  induction run generalizing x with
  | stop lower exponent => simpa [finalExponent, finalLower, steps] using bound
  | next lower exponent shift tail ih =>
      have squared := one_step denominator lower exponent shift
        denominatorPositive x xNonnegative bound
      have tailSound := ih (x := x ^ 2) (by positivity) squared
      simpa [finalExponent, finalLower, steps, pow_succ, pow_mul,
        Nat.mul_comm] using tailSound

end Run

/-- A purely rational certificate that `ratio` has binary rate at least
`rateNumerator / rateDenominator`.  The meaning is expressed by a bounded
dyadic power comparison and a scaled integer exponent comparison, so no real
logarithm or gigantic normalized power is evaluated by the checker. -/
structure ScaledDyadicRateLower
    (ratio : ℚ) (rateNumerator rateDenominator : Nat) where
  steps : Nat
  exponent : Nat
  ratioNonnegative : 0 ≤ ratio
  powerLower : (2 : ℚ) ^ exponent ≤ ratio ^ (2 ^ steps)
  scaledExponent :
    rateNumerator * 2 ^ steps ≤ rateDenominator * exponent

namespace ScaledDyadicRateLower

/-- Convert a bounded rational dyadic-rate certificate and one exact
conditional-fibre product inequality into an integer powered state-count
lower bound.  The extra power `2 ^ steps` is the bounded certificate scale;
no root, logarithm, floating-point number, or gigantic normalized power is
evaluated. -/
theorem nat_state_power_lower
    {safe flat stateCount multiplicity rateNumerator rateDenominator : Nat}
    (certificate : ScaledDyadicRateLower
      ((safe : ℚ) / flat) rateNumerator rateDenominator)
    (flatPositive : 0 < flat)
    (productCost : safe ^ multiplicity ≤ flat ^ multiplicity * stateCount) :
    2 ^ (rateNumerator * multiplicity * 2 ^ certificate.steps) ≤
      stateCount ^ (rateDenominator * 2 ^ certificate.steps) := by
  have flatPositiveQ : (0 : ℚ) < flat := by exact_mod_cast flatPositive
  have productCostQ :
      (safe : ℚ) ^ multiplicity ≤
        (flat : ℚ) ^ multiplicity * stateCount := by
    exact_mod_cast productCost
  have ratioPower_le_state :
      ((safe : ℚ) / flat) ^ multiplicity ≤ stateCount := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos flatPositiveQ multiplicity)).2
    simpa [mul_comm] using productCostQ
  have certificatePower :
      (2 : ℚ) ^ (certificate.exponent * multiplicity) ≤
        (stateCount : ℚ) ^ (2 ^ certificate.steps) := by
    calc
      (2 : ℚ) ^ (certificate.exponent * multiplicity) =
          ((2 : ℚ) ^ certificate.exponent) ^ multiplicity := by
        rw [pow_mul]
      _ ≤ (((safe : ℚ) / flat) ^ (2 ^ certificate.steps)) ^
          multiplicity := by
        exact pow_le_pow_left₀ (by positivity) certificate.powerLower multiplicity
      _ = (((safe : ℚ) / flat) ^ multiplicity) ^
          (2 ^ certificate.steps) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ (stateCount : ℚ) ^ (2 ^ certificate.steps) := by
        exact pow_le_pow_left₀ (by positivity) ratioPower_le_state _
  have scaled :
      rateNumerator * multiplicity * 2 ^ certificate.steps ≤
        rateDenominator * (certificate.exponent * multiplicity) := by
    nlinarith [certificate.scaledExponent]
  have dyadicPower :
      (2 : ℚ) ^ (rateNumerator * multiplicity * 2 ^ certificate.steps) ≤
        ((2 : ℚ) ^ (certificate.exponent * multiplicity)) ^
          rateDenominator := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled)
  have rationalResult :
      (2 : ℚ) ^ (rateNumerator * multiplicity * 2 ^ certificate.steps) ≤
        (stateCount : ℚ) ^ (rateDenominator * 2 ^ certificate.steps) := by
    calc
      _ ≤ ((2 : ℚ) ^ (certificate.exponent * multiplicity)) ^
          rateDenominator := dyadicPower
      _ ≤ ((stateCount : ℚ) ^ (2 ^ certificate.steps)) ^
          rateDenominator :=
        pow_le_pow_left₀ (by positivity) certificatePower rateDenominator
      _ = (stateCount : ℚ) ^
          (rateDenominator * 2 ^ certificate.steps) := by
        rw [← pow_mul, Nat.mul_comm]
  exact_mod_cast rationalResult

end ScaledDyadicRateLower

end StructuralExhaustion.Core.FixedPointRepeatedSquareLower
