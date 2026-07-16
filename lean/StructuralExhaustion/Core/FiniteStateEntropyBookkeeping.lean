import Mathlib.Analysis.SpecialFunctions.Log.Base
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteStateEntropyBookkeeping

universe u

/-!
# Finite-state entropy bookkeeping

This profile records the elementary integer bookkeeping attached to one
*supplied* duplicate-free state collection.  It does not enumerate an ambient
type, construct a Boolean cube, or assert that the listed states realize any
independent choices.  In particular, positivity, realization, injectivity,
and every comparison with a support capacity remain obligations of the
caller.
-/

/-- A local finite state collection together with the support size against
which a later application may compare it.  No relationship between the two
numbers is built into this bookkeeping record. -/
structure Profile where
  State : Type u
  states : Core.OrderedCollection State
  supportSize : Nat

namespace Profile

/-- Exact number of states explicitly supplied by the caller. -/
def stateCount (profile : Profile.{u}) : Nat :=
  profile.states.values.length

/-- Integer bit count attached to the supplied state count.  This is only the
floor logarithm; it carries no realization or capacity assertion. -/
def bitCount (profile : Profile.{u}) : Nat :=
  Nat.log2 profile.stateCount

/-- The manuscript-valued base-two entropy per support element.  Division is
the ordinary totalized division on `ℝ`; applications that use a positive
denominator must separately prove positive support size. -/
noncomputable def normalizedEntropy (profile : Profile.{u}) : ℝ :=
  Real.logb 2 profile.stateCount / profile.supportSize

/-- Bookkeeping performs no semantic predicate calls over the supplied
states.  Length and logarithm evaluation are accounted for separately by
`arithmeticWork`. -/
def semanticChecks (_profile : Profile.{u}) : Nat :=
  0

/-- A conservative local evaluation budget: one traversal to read the list
length, at most `bitCount` logarithmic reductions, and one division node. -/
def arithmeticWork (profile : Profile.{u}) : Nat :=
  profile.stateCount + profile.bitCount + 1

@[simp]
theorem stateCount_eq_values_length (profile : Profile.{u}) :
    profile.stateCount = profile.states.values.length :=
  rfl

@[simp]
theorem bitCount_eq_log2_stateCount (profile : Profile.{u}) :
    profile.bitCount = Nat.log2 profile.stateCount :=
  rfl

@[simp]
theorem normalizedEntropy_eq (profile : Profile.{u}) :
    profile.normalizedEntropy =
      Real.logb 2 profile.stateCount / profile.supportSize :=
  rfl

/-- The executable numerator is exactly the natural floor of the real
base-two logarithm used in `normalizedEntropy`. -/
theorem bitCount_eq_natFloor_logb (profile : Profile.{u}) :
    profile.bitCount = ⌊Real.logb 2 profile.stateCount⌋₊ := by
  rw [profile.bitCount_eq_log2_stateCount, Nat.log2_eq_log_two]
  exact (Real.natFloor_logb_natCast 2 profile.stateCount).symm

@[simp]
theorem semanticChecks_eq_zero (profile : Profile.{u}) :
    profile.semanticChecks = 0 :=
  rfl

/-- The local list/arithmetic work is linear in the supplied state count and
does not depend on any ambient graph or state universe. -/
theorem arithmeticWork_le_two_mul_stateCount_add_one (profile : Profile.{u}) :
    profile.arithmeticWork ≤ 2 * profile.stateCount + 1 := by
  have log_le : profile.bitCount ≤ profile.stateCount := by
    rw [profile.bitCount_eq_log2_stateCount, Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 profile.stateCount
  unfold arithmeticWork
  omega

end Profile

end StructuralExhaustion.Core.FiniteStateEntropyBookkeeping
