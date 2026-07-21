import HypostructureErdos64EG.OfficialStatement

namespace HypostructureErdos64EG

/-!
# Executable dyadic target algebra

The bounded exponent is a finite search space. Its completeness theorem below
keeps the executable predicate equivalent to the unbounded exponent appearing
in `OfficialStatement`.
-/

/-- Executable predicate for cycle lengths accepted by the official theorem. -/
def PowerOfTwoLength (length : Nat) : Prop :=
  ∃ exponent : Fin (length + 1),
    2 ≤ exponent.1 ∧ length = 2 ^ exponent.1

instance powerOfTwoLengthDecidable (length : Nat) :
    Decidable (PowerOfTwoLength length) := by
  unfold PowerOfTwoLength
  infer_instance

private theorem exponent_le_two_pow (exponent : Nat) :
    exponent ≤ 2 ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent inductionHypothesis =>
      rw [pow_succ]
      have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
      omega

/-- The executable predicate is equivalent to the official unbounded form. -/
theorem powerOfTwoLength_iff (length : Nat) :
    PowerOfTwoLength length ↔
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent := by
  constructor
  · rintro ⟨exponent, lower, equality⟩
    exact ⟨exponent.1, lower, equality⟩
  · rintro ⟨exponent, lower, equality⟩
    have bound : exponent < length + 1 := by
      rw [equality]
      exact Nat.lt_succ_of_le (exponent_le_two_pow exponent)
    exact ⟨⟨exponent, bound⟩, lower, equality⟩

/-- Four is the first accepted cycle length. -/
theorem powerOfTwoLength_four : PowerOfTwoLength 4 := by
  exact ⟨⟨2, by decide⟩, by decide, by decide⟩

/-- Executable return length whose successor is an accepted cycle length. -/
def MersenneLength (length : Nat) : Prop :=
  PowerOfTwoLength (length + 1)

instance mersenneLengthDecidable (length : Nat) :
    Decidable (MersenneLength length) :=
  powerOfTwoLengthDecidable (length + 1)

/-- The executable return lengths are exactly `2^k - 1` for `k ≥ 2`. -/
theorem mersenneLength_iff (length : Nat) :
    MersenneLength length ↔
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent - 1 := by
  rw [MersenneLength, powerOfTwoLength_iff]
  constructor
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
    omega
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
    omega

/-- The manuscript's Mersenne return-length set. -/
def MersenneSet : Set Nat := {length | MersenneLength length}

end HypostructureErdos64EG
