import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteBitRelationBarrier

/-!
# Finite relation-barrier counts

This module owns the integer arithmetic behind a finite two-leg relation
barrier.  A row at length `s` records the labels compatible with one source
label.  For lengths `a` and `b`, `safeCount` counts triples whose two legs are
compatible, while `flatCount` additionally requires the composed `a+b` leg.

The implementation uses bit-row intersections.  It does not enumerate a
family of ambient objects or a Boolean state cube.
-/

/-- A length-indexed family of Boolean relation matrices on `size` labels. -/
structure Profile (size : Nat) where
  row : Nat → Fin size → BitVec size

namespace Profile

variable {size : Nat} (profile : Profile size)

/-- Number of compatible two-leg triples, summed by their middle label. -/
def safeCount (leftLength rightLength : Nat) : Nat :=
  ∑ middle : Fin size,
    (profile.row leftLength middle).cpop.toNat *
      (profile.row rightLength middle).cpop.toNat

/-- Number of two-leg triples whose composed leg is also compatible. -/
def flatCount (leftLength rightLength : Nat) : Nat :=
  ∑ source : Fin size, ∑ middle : Fin size,
    if (profile.row leftLength source).getLsb middle then
      (((profile.row rightLength middle) &&&
        (profile.row (leftLength + rightLength) source)).cpop).toNat
    else 0

/-- The complementary, composition-obstructed triple count. -/
def obstructedCount (leftLength rightLength : Nat) : Nat :=
  profile.safeCount leftLength rightLength -
    profile.flatCount leftLength rightLength

theorem obstructed_add_flat
    (leftLength rightLength : Nat)
    (flat_le : profile.flatCount leftLength rightLength ≤
      profile.safeCount leftLength rightLength) :
    profile.obstructedCount leftLength rightLength +
        profile.flatCount leftLength rightLength =
      profile.safeCount leftLength rightLength := by
  exact Nat.sub_add_cancel flat_le

/-- Primitive bit operations used by one barrier count. -/
def checks (_leftLength _rightLength : Nat) : Nat :=
  let _relation := profile.row
  size + size ^ 2

theorem checks_quadratic (leftLength rightLength : Nat) :
    profile.checks leftLength rightLength ≤ 2 * (size + 1) ^ 2 := by
  simp only [checks]
  nlinarith [Nat.zero_le size]

end Profile

end StructuralExhaustion.Core.FiniteBitRelationBarrier
