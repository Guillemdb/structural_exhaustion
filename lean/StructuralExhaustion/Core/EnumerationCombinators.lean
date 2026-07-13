import StructuralExhaustion.Core.FiniteSearch
import Mathlib.Data.Fintype.Card

namespace StructuralExhaustion.Core

universe u v

/-!
Constructive combinators for explicit Mathlib finite enumerations.

The order produced by every combinator is part of its API.  Products are
lexicographic in the two input enumeration orders.  Bounded lists are ordered
first by the empty list and then recursively by head and tail, following the
input enumeration order at each position.
-/

/-- Lists over `α` whose length is at most `bound`. -/
abbrev BoundedList (α : Type u) (bound : Nat) :=
  { xs : List α // xs.length ≤ bound }

namespace BoundedList

/-- Prepend one element while raising the length bound by one. -/
private def cons {α : Type u} {bound : Nat} (head : α)
    (tail : BoundedList α bound) : BoundedList α (bound + 1) :=
  ⟨head :: tail.1, Nat.succ_le_succ tail.2⟩

/-- The raw, already duplicate-free list underlying `boundedList`. -/
private def elems {α : Type u} (alphabet : List α) :
    (bound : Nat) → List (BoundedList α bound)
  | 0 => [⟨[], Nat.zero_le 0⟩]
  | bound + 1 =>
      ⟨[], Nat.zero_le (bound + 1)⟩ ::
        alphabet.flatMap fun head =>
          (elems alphabet bound).map (cons head)

private theorem elems_nodup {α : Type u} {alphabet : List α}
    (alphabetNodup : alphabet.Nodup) :
    ∀ bound, (elems alphabet bound).Nodup := by
  intro bound
  induction bound with
  | zero => simp [elems]
  | succ bound ih =>
      simp only [elems, List.nodup_cons]
      constructor
      · simp [cons]
      · rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
        constructor
        · intro head _
          exact ih.map (by
            intro left right same
            apply Subtype.ext
            exact (List.cons.inj (congrArg Subtype.val same)).2)
        · exact alphabetNodup.imp fun {left right} leftNeRight => by
            intro leftOutput leftMem rightOutput rightMem same
            rcases List.mem_map.1 leftMem with ⟨leftTail, _, rfl⟩
            rcases List.mem_map.1 rightMem with ⟨rightTail, _, rfl⟩
            apply leftNeRight
            exact (List.cons.inj (congrArg Subtype.val same)).1

private theorem mem_elems {α : Type u} (enumeration : FinEnum α) :
    ∀ {bound} (xs : BoundedList α bound),
      xs ∈ elems enumeration.orderedValues bound := by
  intro bound
  induction bound with
  | zero =>
      intro xs
      have empty : xs.1 = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero xs.2)
      have xsEq : xs = ⟨[], Nat.zero_le 0⟩ := Subtype.ext empty
      simp [elems, xsEq]
  | succ bound ih =>
      intro xs
      rcases xs with ⟨values, lengthBound⟩
      cases values with
      | nil => simp [elems]
      | cons head tail =>
        have tailBound : tail.length ≤ bound := by
          simpa using Nat.le_of_succ_le_succ lengthBound
        let boundedTail : BoundedList α bound := ⟨tail, tailBound⟩
        have headMem : head ∈ enumeration.orderedValues :=
          enumeration.mem_orderedValues head
        have tailMem : boundedTail ∈ elems enumeration.orderedValues bound := ih boundedTail
        simp only [elems, List.mem_cons]
        right
        apply List.mem_flatMap_of_mem headMem
        have mapped : cons head boundedTail ∈
            (elems enumeration.orderedValues bound).map (cons head) :=
          List.mem_map_of_mem tailMem
        simpa [boundedTail, cons] using mapped

end BoundedList

namespace Enumeration

/-- Every duplicate-free list over an exactly enumerated finite type is no
longer than the full enumeration. -/
theorem length_le_elems_of_nodup {α : Type u}
    (enumeration : FinEnum α) {values : List α}
    (valuesNodup : values.Nodup) :
    values.length ≤ enumeration.orderedValues.length := by
  letI : FinEnum α := enumeration
  simpa [FinEnum.orderedValues, FinEnum.toList,
    FinEnum.card_eq_fintypeCard] using valuesNodup.length_le_card

/-- Package a duplicate-free list over an exactly enumerated finite type with
the canonical enumeration-cardinality bound. -/
def boundedListOfNodup {α : Type u} (enumeration : FinEnum α)
    (values : List α) (valuesNodup : values.Nodup) :
    BoundedList α enumeration.orderedValues.length :=
  ⟨values, length_le_elems_of_nodup enumeration valuesNodup⟩

/-- Lexicographic product of two exact ordered enumerations. -/
@[implicit_reducible]
def prod {α : Type u} {β : Type v}
    (left : FinEnum α) (right : FinEnum β) : FinEnum (α × β) := by
  letI : FinEnum α := left
  letI : FinEnum β := right
  exact inferInstance

/-- Exact enumeration of a subtype selected by a decidable predicate.

The enumeration retains the source order and removes precisely
the values for which the predicate is false. -/
@[implicit_reducible]
def subtype {α : Type u} (enumeration : FinEnum α)
    (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    FinEnum {value // predicate value} := by
  letI : FinEnum α := enumeration
  letI : DecidablePred predicate := decidePredicate
  exact inferInstance

/-- Exact ordered enumeration of all lists of length at most `bound`. -/
@[implicit_reducible]
def boundedList {α : Type u} (enumeration : FinEnum α)
    (bound : Nat) : FinEnum (BoundedList α bound) :=
  @FinEnum.ofNodupList (BoundedList α bound)
    (letI : DecidableEq α := enumeration.decEq; inferInstance)
    (BoundedList.elems enumeration.orderedValues bound)
    (BoundedList.mem_elems enumeration)
    (BoundedList.elems_nodup enumeration.nodup_orderedValues bound)

/-- Decide a universal property by exhaustively searching an exact finite
enumeration for a counterexample.  Problem instances supply only the
pointwise decision procedure; completeness is inherited from `FinEnum`. -/
def forallDecidable {α : Type u} (enumeration : FinEnum α)
    (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    Decidable (∀ value, predicate value) := by
  letI : FinEnum α := enumeration
  letI : DecidablePred predicate := decidePredicate
  exact Fintype.decidableForallFintype

end Enumeration

end StructuralExhaustion.Core
