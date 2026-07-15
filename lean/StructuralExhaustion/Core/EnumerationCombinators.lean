import StructuralExhaustion.Core.FiniteSearch
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

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
    FinEnum {value // predicate value} :=
  let accepted : List {value // predicate value} :=
    enumeration.orderedValues.filterMap fun value =>
      if accepted : predicate value then some ⟨value, accepted⟩ else none
  @FinEnum.ofNodupList {value // predicate value}
    (by
      letI : DecidableEq α := enumeration.decEq
      infer_instance)
    accepted
    (by
      rintro ⟨value, acceptedValue⟩
      simp [accepted, acceptedValue])
    (by
      apply enumeration.nodup_orderedValues.filterMap
      intro left right output leftOutput rightOutput
      by_cases leftAccepted : predicate left
      · simp [leftAccepted] at leftOutput
        by_cases rightAccepted : predicate right
        · simp [rightAccepted] at rightOutput
          exact congrArg Subtype.val
            (leftOutput.trans rightOutput.symm)
        · simp [rightAccepted] at rightOutput
      · simp [leftAccepted] at leftOutput)

/-- Restricting an exact finite enumeration to a decidable subtype cannot
increase its cardinality. -/
theorem subtype_card_le {α : Type u} (enumeration : FinEnum α)
    (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    (subtype enumeration predicate decidePredicate).card ≤ enumeration.card := by
  letI : FinEnum α := enumeration
  letI : FinEnum {value // predicate value} :=
    subtype enumeration predicate decidePredicate
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- An unordered pair of distinct values. -/
abbrev DistinctPair (α : Type u) := {pair : Sym2 α // ¬pair.IsDiag}

/-- Exact ordered enumeration of `Sym2 α`, derived from the supplied item
order.  Duplicate quotient representatives are removed by `FinEnum.ofList`;
the construction touches only item labels. -/
@[implicit_reducible]
def sym2 {α : Type u} (enumeration : FinEnum α) : FinEnum (Sym2 α) := by
  letI : DecidableEq α := enumeration.decEq
  let values := enumeration.orderedValues.flatMap fun left ↦
    enumeration.orderedValues.map fun right ↦ s(left, right)
  apply FinEnum.ofList values
  intro pair
  induction pair using Sym2.inductionOn with
  | _ left right =>
      simp only [values, List.mem_flatMap, List.mem_map]
      exact ⟨left, enumeration.mem_orderedValues left,
        right, enumeration.mem_orderedValues right, rfl⟩

/-- Exact finite enumeration of unordered distinct pairs.  It is derived from
the supplied item enumeration and never materializes any ambient structure
carried by the items. -/
@[implicit_reducible]
def distinctPairs {α : Type u} (enumeration : FinEnum α) :
    FinEnum (DistinctPair α) :=
  subtype (sym2 enumeration) (fun pair ↦ ¬pair.IsDiag)
    (fun _pair ↦ inferInstance)

/-- The local pair schedule has exactly `choose n 2` entries. -/
theorem distinctPairs_card {α : Type u} (enumeration : FinEnum α) :
    (distinctPairs enumeration).card = Nat.choose enumeration.card 2 := by
  letI : FinEnum α := enumeration
  letI : FinEnum (DistinctPair α) := distinctPairs enumeration
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Sym2.card_subtype_not_diag

/-- Pair generation is quadratically bounded in the explicit item count. -/
theorem distinctPairs_card_le_square {α : Type u}
    (enumeration : FinEnum α) :
    (distinctPairs enumeration).card ≤ enumeration.card ^ 2 := by
  rw [distinctPairs_card]
  exact Nat.choose_le_pow _ _

/-- A canonically oriented pair: the first item precedes the second in the
explicit enumeration order. -/
abbrev OrderedDistinctPair {α : Type u} (enumeration : FinEnum α) :=
  {pair : α × α //
    (enumeration.equiv pair.1).1 < (enumeration.equiv pair.2).1}

/-- Exact enumeration of canonically oriented distinct pairs.  This form is
convenient for local graph certificates whose two endpoints have dependent
types or roles. -/
@[implicit_reducible]
def orderedDistinctPairs {α : Type u} (enumeration : FinEnum α) :
    FinEnum (OrderedDistinctPair enumeration) :=
  subtype (prod enumeration enumeration)
    (fun pair ↦ (enumeration.equiv pair.1).1 <
      (enumeration.equiv pair.2).1)
    (fun _pair ↦ inferInstance)

/-- Forget the canonical orientation of a distinct pair. -/
def orderedDistinctPairToDistinctPair {α : Type u}
    {enumeration : FinEnum α}
    (pair : OrderedDistinctPair enumeration) : DistinctPair α :=
  ⟨s(pair.1.1, pair.1.2), by
    rw [Sym2.mk_isDiag_iff]
    intro equal
    exact (Nat.ne_of_lt pair.2)
      (congrArg (fun value => (enumeration.equiv value).1) equal)⟩

theorem orderedDistinctPairToDistinctPair_bijective {α : Type u}
    (enumeration : FinEnum α) :
    Function.Bijective
      (@orderedDistinctPairToDistinctPair α enumeration) := by
  constructor
  · intro left right equal
    apply Subtype.ext
    have symEqual : s(left.1.1, left.1.2) = s(right.1.1, right.1.2) :=
      congrArg Subtype.val equal
    rw [Sym2.eq_iff] at symEqual
    rcases symEqual with direct | swapped
    · exact Prod.ext direct.1 direct.2
    · exfalso
      have leftLt := left.2
      have rightLt := right.2
      rw [swapped.1, swapped.2] at leftLt
      exact (Nat.not_lt_of_ge (Nat.le_of_lt rightLt)) leftLt
  · intro pair
    rcases pair with ⟨value, notDiag⟩
    induction value using Sym2.inductionOn with
    | _ left right =>
        have distinct : left ≠ right := by
          simpa [Sym2.mk_isDiag_iff] using notDiag
        have rankDistinct : enumeration.equiv left ≠ enumeration.equiv right :=
          fun equal => distinct (enumeration.equiv.injective equal)
        rcases lt_or_gt_of_ne rankDistinct with before | after
        · let ordered : OrderedDistinctPair enumeration :=
            ⟨(left, right), before⟩
          exact ⟨ordered, rfl⟩
        · let ordered : OrderedDistinctPair enumeration :=
            ⟨(right, left), after⟩
          exact ⟨ordered, by
            apply Subtype.ext
            exact Sym2.eq_swap⟩

/-- Canonical orientation changes no cardinality: there is exactly one entry
for every unordered two-element subset. -/
theorem orderedDistinctPairs_card {α : Type u}
    (enumeration : FinEnum α) :
    (orderedDistinctPairs enumeration).card = Nat.choose enumeration.card 2 := by
  letI : FinEnum α := enumeration
  letI : FinEnum (OrderedDistinctPair enumeration) :=
    orderedDistinctPairs enumeration
  letI : FinEnum (DistinctPair α) := distinctPairs enumeration
  calc
    (orderedDistinctPairs enumeration).card =
        Fintype.card (OrderedDistinctPair enumeration) :=
      FinEnum.card_eq_fintypeCard
    _ = Fintype.card (DistinctPair α) :=
      Fintype.card_congr
        (Equiv.ofBijective orderedDistinctPairToDistinctPair
          (orderedDistinctPairToDistinctPair_bijective enumeration))
    _ = (distinctPairs enumeration).card :=
      FinEnum.card_eq_fintypeCard.symm
    _ = Nat.choose enumeration.card 2 := distinctPairs_card enumeration

/-- Exact quadratic form of the unordered-pair count. -/
theorem two_mul_choose_two_add (count : Nat) :
    2 * Nat.choose count 2 + count = count ^ 2 := by
  induction count with
  | zero => decide
  | succ count inductionHypothesis =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      change 2 * (count + Nat.choose count 2) + (count + 1) =
        (count + 1) ^ 2
      calc
        2 * (count + Nat.choose count 2) + (count + 1) =
            (2 * Nat.choose count 2 + count) + 2 * count + 1 := by ring
        _ = count ^ 2 + 2 * count + 1 := by rw [inductionHypothesis]
        _ = (count + 1) ^ 2 := by ring

namespace OrderedDistinctPair

variable {α : Type u} {enumeration : FinEnum α}

def first (pair : OrderedDistinctPair enumeration) : α := pair.1.1
def second (pair : OrderedDistinctPair enumeration) : α := pair.1.2

theorem distinct (pair : OrderedDistinctPair enumeration) :
    pair.first ≠ pair.second := by
  intro equal
  exact (Nat.ne_of_lt pair.2)
    (congrArg (fun value ↦ (enumeration.equiv value).1) equal)

end OrderedDistinctPair

/-- Canonical pair generation is quadratically bounded in the declared item
count. -/
theorem orderedDistinctPairs_card_le_square {α : Type u}
    (enumeration : FinEnum α) :
    (orderedDistinctPairs enumeration).card ≤ enumeration.card ^ 2 := by
  calc
    (orderedDistinctPairs enumeration).card ≤
        (prod enumeration enumeration).card :=
      subtype_card_le (prod enumeration enumeration)
        (fun pair ↦ (enumeration.equiv pair.1).1 <
          (enumeration.equiv pair.2).1)
        (fun _pair ↦ inferInstance)
    _ = enumeration.card ^ 2 := by
      letI : FinEnum α := enumeration
      letI : FinEnum (α × α) := prod enumeration enumeration
      rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
      simp [pow_two]

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
