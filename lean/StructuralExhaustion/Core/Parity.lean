import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.ModEq

namespace StructuralExhaustion.Core.Parity

/-! The two-class parity label used by capacity arguments. -/

/-- Boolean label for the even congruence class. -/
def label (value : Nat) : Bool :=
  decide (Even value)

/-- Equality of parity labels is Mathlib congruence modulo two. -/
theorem modEq_two_of_label_eq {left right : Nat}
    (equal : label left = label right) : left ≡ right [MOD 2] := by
  by_cases leftEven : Even left
  · have leftLabel : label left = true := by simp [label, leftEven]
    have rightLabel : label right = true := equal.symm.trans leftLabel
    have rightEven : Even right := by
      exact of_decide_eq_true (by simpa [label] using rightLabel)
    exact (Nat.even_iff.mp leftEven).trans (Nat.even_iff.mp rightEven).symm
  · have leftLabel : label left = false := by simp [label, leftEven]
    have rightLabel : label right = false := equal.symm.trans leftLabel
    have rightOdd : ¬ Even right := by
      exact of_decide_eq_false (by simpa [label] using rightLabel)
    exact (Nat.not_even_iff.mp leftEven).trans (Nat.not_even_iff.mp rightOdd).symm

/-- Equality of the two Boolean parity labels is exact equality modulo two. -/
theorem mod_two_eq_of_label_eq {left right : Nat}
    (equal : label left = label right) : left % 2 = right % 2 :=
  modEq_two_of_label_eq equal

end StructuralExhaustion.Core.Parity
