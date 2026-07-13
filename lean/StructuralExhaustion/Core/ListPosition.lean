import Mathlib.Data.List.Basic

namespace StructuralExhaustion.Core.ListPosition

universe u

/-! Constructive facts about canonical `List.idxOf` positions. -/

/-- Looking up the canonical index of a member returns that member. -/
theorem getElem_idxOf_of_mem {α : Type u} [DecidableEq α]
    {values : List α} {item : α} (member : item ∈ values) :
    values[values.idxOf item]'(List.idxOf_lt_length_of_mem member) = item := by
  have lookup := List.getElem?_idxOf member
  rw [List.getElem?_eq_getElem
    (List.idxOf_lt_length_of_mem member)] at lookup
  exact Option.some.inj lookup

/-- Canonical positions are injective on values known to occur in a list. -/
theorem idxOf_injective_on_mem {α : Type u} [DecidableEq α]
    {values : List α} {left right : α}
    (leftMem : left ∈ values)
    (equal : values.idxOf left = values.idxOf right) : left = right := by
  exact (List.idxOf_inj leftMem).mp equal

/-- The canonical list positions of two distinct listed values, packaged with
all bounds and lookup equations needed by downstream semantic adapters. -/
structure LocatedDistinctPair {α : Type u} [DecidableEq α] (values : List α)
    (first second : α) where
  left : Nat
  right : Nat
  left_eq : left = values.idxOf first
  right_eq : right = values.idxOf second
  left_lt : left < values.length
  right_lt : right < values.length
  left_value : values[left] = first
  right_value : values[right] = second
  positions_distinct : left ≠ right

/-- Locate two distinct members once.  Applications receive canonical
positions, bounds, lookups, and position distinctness as one reusable value. -/
def locateDistinctPair {α : Type u} [DecidableEq α]
    {values : List α} {first second : α}
    (firstMem : first ∈ values) (secondMem : second ∈ values)
    (different : first ≠ second) :
    LocatedDistinctPair values first second where
  left := values.idxOf first
  right := values.idxOf second
  left_eq := rfl
  right_eq := rfl
  left_lt := List.idxOf_lt_length_of_mem firstMem
  right_lt := List.idxOf_lt_length_of_mem secondMem
  left_value := getElem_idxOf_of_mem firstMem
  right_value := getElem_idxOf_of_mem secondMem
  positions_distinct := by
    intro equal
    exact different (idxOf_injective_on_mem firstMem equal)

end StructuralExhaustion.Core.ListPosition
