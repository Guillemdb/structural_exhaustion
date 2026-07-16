import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FinitePowerScaleSplit

/-!
# Constant-work finite power-scale split

This module owns the exact arithmetic branch used when a proof has already
supplied a finite support and a finite state count.  The runner compares the
two natural powers once.  It does not enumerate states, supports, functions,
graphs, or any ambient universe.
-/

/-- The four natural numbers occurring in a finite power threshold.  The
profile deliberately carries no semantic claim about how these values were
obtained; applications retain that provenance in their own verified stage. -/
structure Profile where
  base : Nat
  supportSize : Nat
  stateCount : Nat
  scale : Nat
  deriving Repr, DecidableEq

namespace Profile

/-- The exact two outcomes of the power comparison. -/
inductive Outcome (profile : Profile) : Type
  | upper
      (bound : profile.base ^ profile.supportSize ≤
        profile.stateCount ^ profile.scale)
  | lower
      (strict : profile.stateCount ^ profile.scale <
        profile.base ^ profile.supportSize)

/-- Decide one natural-number comparison.  This performs no finite scan. -/
def run (profile : Profile) : profile.Outcome := by
  by_cases bound :
      profile.base ^ profile.supportSize ≤
        profile.stateCount ^ profile.scale
  · exact .upper bound
  · exact .lower (by omega)

/-- Every supplied profile follows exactly one of the two comparison
branches. -/
theorem exhaustive (profile : Profile) :
    profile.base ^ profile.supportSize ≤ profile.stateCount ^ profile.scale ∨
      profile.stateCount ^ profile.scale < profile.base ^ profile.supportSize := by
  cases profile.run with
  | upper bound => exact Or.inl bound
  | lower strict => exact Or.inr strict

/-- Taking base-two logarithms of the upper power branch gives the exact
weighted logarithmic budget.  Positivity is required only for the supplied
state count; the zero-base case is handled by the totalized real logarithm.
No state or support family is inspected. -/
theorem logb_budget_of_upper (profile : Profile)
    (stateCountPos : 0 < profile.stateCount)
    (upper : profile.base ^ profile.supportSize ≤
      profile.stateCount ^ profile.scale) :
    (profile.supportSize : ℝ) * Real.logb 2 profile.base ≤
      (profile.scale : ℝ) * Real.logb 2 profile.stateCount := by
  by_cases baseZero : profile.base = 0
  · rw [baseZero]
    simp only [Nat.cast_zero, Real.logb_zero, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg profile.scale)
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast stateCountPos))
  · have basePos : 0 < profile.base := Nat.pos_of_ne_zero baseZero
    have castUpper :
        (profile.base : ℝ) ^ profile.supportSize ≤
          (profile.stateCount : ℝ) ^ profile.scale := by
      exact_mod_cast upper
    have logged := Real.logb_le_logb_of_le (b := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (profile.base : ℝ) ^ profile.supportSize)
      castUpper
    simpa only [Real.logb_pow] using logged

/-- The number of proof-level arithmetic comparisons made by `run`. -/
def checks (_profile : Profile) : Nat := 1

@[simp]
theorem checks_eq_one (profile : Profile) : profile.checks = 1 :=
  rfl

/-- A proof-carrying execution of the exact split. -/
structure VerifiedStage (profile : Profile) : Type where
  outcome : profile.Outcome
  total :
    profile.base ^ profile.supportSize ≤ profile.stateCount ^ profile.scale ∨
      profile.stateCount ^ profile.scale < profile.base ^ profile.supportSize
  work : profile.checks = 1

/-- Execute and package the split, its exhaustive semantics, and its exact
constant work ledger. -/
def verifiedStage (profile : Profile) : profile.VerifiedStage where
  outcome := profile.run
  total := profile.exhaustive
  work := profile.checks_eq_one

end Profile

end StructuralExhaustion.Core.FinitePowerScaleSplit
