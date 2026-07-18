import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace StructuralExhaustion.Core.BoundedListCode

universe u

/-!
# Symbolic codes for bounded observed lists

An observed list of length at most `bound` is padded by `none` into a fixed
function `Fin bound → Option α`.  Encoding reads only the supplied list.  It
does not enumerate `α`, the list space, or the resulting function alphabet.
-/

abbrev BoundedList (α : Type u) (bound : Nat) :=
  {values : List α // values.length ≤ bound}

abbrev Code (α : Type u) (bound : Nat) := Fin bound → Option α

def encode {α : Type u} {bound : Nat}
    (values : BoundedList α bound) : Code α bound :=
  fun index => values.1[index.1]?

theorem encode_injective {α : Type u} {bound : Nat} :
    Function.Injective (@encode α bound) := by
  intro left right equal
  apply Subtype.ext
  apply List.ext_getElem?
  intro index
  by_cases inBound : index < bound
  · exact congrFun equal ⟨index, inBound⟩
  · have boundLe : bound ≤ index := Nat.le_of_not_gt inBound
    rw [List.getElem?_eq_none_iff.mpr (left.2.trans boundLe),
      List.getElem?_eq_none_iff.mpr (right.2.trans boundLe)]

theorem code_card (α : Type u) [Fintype α] (bound : Nat) :
    Fintype.card (Code α bound) = (Fintype.card α + 1) ^ bound := by
  classical
  simp [Code]

noncomputable def optionEquivFinOfEquiv {α : Type u} {card : Nat}
    (equiv : α ≃ Fin card) : Option α ≃ Fin (card + 1) :=
  (Equiv.optionCongr equiv).trans (finSuccEquiv card).symm

noncomputable def functionEquivFinOfEquiv {β : Type u} {base : Nat}
    (equiv : β ≃ Fin base) :
    (n : Nat) → (Fin n → β) ≃ Fin (base ^ n)
  | 0 => {
      toFun := fun _ => 0
      invFun := fun _ index => Fin.elim0 index
      left_inv := by
        intro value
        funext index
        exact Fin.elim0 index
      right_inv := by
        intro value
        ext
        simp
    }
  | n + 1 =>
      (Fin.succFunEquiv β n).trans <|
        ((functionEquivFinOfEquiv equiv n).prodCongr equiv).trans <|
          finProdFinEquiv.trans <|
            finCongr (by rw [pow_succ])

noncomputable def codeEquivFinOfEquiv {α : Type u} {card : Nat}
    (equiv : α ≃ Fin card) (bound : Nat) :
    Code α bound ≃ Fin ((card + 1) ^ bound) :=
  functionEquivFinOfEquiv (optionEquivFinOfEquiv equiv) bound

theorem codeEquivFinOfEquiv_injective {α : Type u} {card : Nat}
    (equiv : α ≃ Fin card) (bound : Nat) :
    Function.Injective (codeEquivFinOfEquiv equiv bound) :=
  (codeEquivFinOfEquiv equiv bound).injective

end StructuralExhaustion.Core.BoundedListCode
