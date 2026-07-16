import Mathlib.Tactic

namespace StructuralExhaustion.Core.FinitePoweredBudgetTransfer

/-!
# Symbolic powered-budget transfer

This profile isolates the arithmetic used when a one-step forced cost is
bounded by a flat cost times a supplied state count, while a preceding branch
bounds a power of that state count strictly below an upper allowance.  The
result is proved symbolically.  No power is evaluated and no finite family is
constructed or scanned.
-/

/-- Exact natural-number inputs for one powered-budget transfer. -/
structure Profile where
  forced : Nat
  flat : Nat
  stateCount : Nat
  upper : Nat
  scale : Nat
  forced_le_flat_mul_stateCount : forced ≤ flat * stateCount
  stateCount_pow_lt_upper : stateCount ^ scale < upper
  flat_pos : 0 < flat

namespace Profile

/-- Symbolic arithmetic transport performs no semantic checks. -/
def checks (_profile : Profile) : Nat := 0

@[simp]
theorem checks_eq_zero (profile : Profile) : profile.checks = 0 := rfl

/-- Raising the supplied one-step bound to the same scale as the strict state
bound yields the strict powered fit. -/
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

end Profile

/-- Function-form API for callers that already own the four arithmetic
certificates and do not need to retain a profile value. -/
theorem forced_pow_lt_flat_pow_mul_upper
    {forced flat stateCount upper scale : Nat}
    (forcedLe : forced ≤ flat * stateCount)
    (statePowLt : stateCount ^ scale < upper)
    (flatPos : 0 < flat) :
    forced ^ scale < flat ^ scale * upper :=
  (Profile.mk forced flat stateCount upper scale forcedLe statePowLt flatPos).forced_pow_lt_flat_pow_mul_upper

end StructuralExhaustion.Core.FinitePoweredBudgetTransfer
