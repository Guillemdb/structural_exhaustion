import StructuralExhaustion.Core.BinaryLogNormalization

namespace StructuralExhaustion.Examples.BinaryLogNormalization

open Filter Asymptotics

/-!
# A non-Erdős binary-budget normalization

This small fixture checks the reusable producer on an unrelated local coding
budget: `n` records each receive a binary word, with one extra rounding bit
per record.  The exact budget and printed floor-log term are natural numbers.
-/

def exactBinaryBudget (n : Nat) : Nat :=
  n * (Nat.log 2 n + 1)

def printedBinaryBudget (n : Nat) : Nat :=
  n * Nat.log 2 n

noncomputable def binaryBudgetRealError (n : Nat) : ℝ :=
  (n : ℝ) * Real.log 2

theorem exactBinaryBudget_real_upper (n : Nat) (hn : n ≠ 0) :
    (exactBinaryBudget n : ℝ) * Real.log 2 ≤
      (n : ℝ) * Real.log n + binaryBudgetRealError n := by
  have floorBound :=
    StructuralExhaustion.Core.BinaryLogNormalization.natLog_two_mul_realLog_le n hn
  unfold exactBinaryBudget binaryBudgetRealError
  push_cast
  nlinarith [show (0 : ℝ) ≤ n by positivity, Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem exactBinaryBudget_sub_printed_le (n : Nat) (hn : n ≠ 0) :
    ((exactBinaryBudget n - printedBinaryBudget n : Nat) : ℝ) ≤
      binaryBudgetRealError n / Real.log 2 + n := by
  have bound :=
    StructuralExhaustion.Core.BinaryLogNormalization.natSub_cast_le_roundingEnvelope
      (exactBinaryBudget n) (printedBinaryBudget n) n 1
        (binaryBudgetRealError n) hn (by norm_num)
        (by unfold binaryBudgetRealError; positivity)
        (by simpa using exactBinaryBudget_real_upper n hn)
        (by
          unfold printedBinaryBudget
          push_cast
          ring)
  simpa using bound

theorem binaryBudgetRealError_isLittleO :
    binaryBudgetRealError =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  unfold binaryBudgetRealError
  simpa [mul_comm] using
    StructuralExhaustion.Core.DiscreteLinearLittleO.const_mul_natCast_isLittleO_natCast_mul_log
      (Real.log 2)

theorem binaryBudgetRoundingEnvelope_isLittleO :
    (fun n : Nat => binaryBudgetRealError n / Real.log 2 + (n : ℝ)) =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  simpa using
    StructuralExhaustion.Core.BinaryLogNormalization.roundingEnvelope_isLittleO
      binaryBudgetRealError binaryBudgetRealError_isLittleO 1

end StructuralExhaustion.Examples.BinaryLogNormalization
