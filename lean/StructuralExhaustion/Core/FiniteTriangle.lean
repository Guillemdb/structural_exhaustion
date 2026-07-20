import StructuralExhaustion.Core.Enumeration
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteTriangle

/-!
# Symbolic finite triangular tables

Many finite classifiers use ordered pairs of coordinates from `Fin (n + 1)`
and retain exactly the strict lower triangle `left + right < n`.  The
equivalence below turns that predicate subtype into the dependent family
`Sigma fun left : Fin n => Fin (n - left)`.  Applications can therefore
certify the final small arithmetic sum without reducing the source product
enumeration or filtering a table.
-/

/-- The strict lower triangle in the square `(Fin (n + 1))²`. -/
abbrev Pair (n : Nat) :=
  {pair : Fin (n + 1) × Fin (n + 1) // pair.1.1 + pair.2.1 < n}

/-- Symbolic dependent-coordinate presentation of a strict finite triangle. -/
def pairEquivSigma (n : Nat) :
    Pair n ≃ Sigma (fun left : Fin n => Fin (n - left.1)) where
  toFun pair :=
    let left : Fin n := ⟨pair.1.1.1, by
      have accepted := pair.2
      omega⟩
    Sigma.mk left ⟨pair.1.2.1, by
      dsimp [left]
      have accepted := pair.2
      omega⟩
  invFun pair :=
    ⟨(⟨pair.1.1, by omega⟩, ⟨pair.2.1, by omega⟩), by
      change pair.1.1 + pair.2.1 < n
      omega⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv pair := by
    rcases pair with ⟨left, right⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl

/-- The strict-triangle cardinality is the sum of its dependent row widths.

This theorem owns all subtype, equivalence, and `Fintype` bookkeeping.  A
fixed application only evaluates the short one-dimensional sum prescribed by
its local table.
-/
theorem card_eq_sum (n : Nat) :
    Fintype.card (Pair n) = ∑ left : Fin n, (n - left.1) := by
  rw [Fintype.card_congr (pairEquivSigma n), Fintype.card_sigma]
  simp only [Fintype.card_fin]

/-- `Nat.card` form used when an application starts from an explicit
`FinEnum` and should not install that enumeration as a global instance. -/
theorem natCard_eq_sum (n : Nat) :
    Nat.card (Pair n) = ∑ left : Fin n, (n - left.1) := by
  rw [Nat.card_eq_fintype_card, card_eq_sum]

end StructuralExhaustion.Core.FiniteTriangle
