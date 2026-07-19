import StructuralExhaustion.Core.FiniteSearch
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.PowersetCard
import Mathlib.SetTheory.Cardinal.Finite
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

/-- `Nat.card` of an explicitly enumerated carrier is the cardinality of that
enumeration.  This bridge owns the temporary `Fintype`/`Finite` instances
needed by Mathlib cardinality theorems. -/
theorem natCard_eq {α : Type u} (enumeration : FinEnum α) :
    Nat.card α = enumeration.card := by
  letI : FinEnum α := enumeration
  rw [Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard]

/-- Every locally owned `Finset` fits in the exact enumeration of its carrier.
Applications supply the graph-derived set and do not reinstall enumeration
instances merely to invoke `Finset.card_le_univ`. -/
theorem finset_card_le {α : Type u} (enumeration : FinEnum α)
    (selected : Finset α) : selected.card ≤ enumeration.card := by
  letI : FinEnum α := enumeration
  simpa [FinEnum.card_eq_fintypeCard] using Finset.card_le_univ selected

/-- Compare two exact local finite carriers through an injective semantic
map, with all `Fintype` instance conversion owned by the framework. -/
theorem card_le_of_injective {α : Type u} {β : Type v}
    (source : FinEnum α) (target : FinEnum β)
    (map : α → β) (injective : Function.Injective map) :
    source.card ≤ target.card := by
  letI : FinEnum α := source
  letI : FinEnum β := target
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective map injective

/-- A duplicate-free list of fixed-cardinality subsets fits in the symbolic
binomial capacity of its explicitly enumerated ground carrier.  The proof
uses only cardinal identities; it never enumerates the powerset. -/
theorem powersetCard_list_length_le {α : Type u}
    (enumeration : FinEnum α) (count : Nat)
    (values : List (Set.powersetCard α count)) (nodup : values.Nodup) :
    values.length ≤ Nat.choose enumeration.card count := by
  letI : FinEnum α := enumeration
  letI : Fintype α := @FinEnum.instFintype _ enumeration
  calc
    values.length ≤ Fintype.card (Set.powersetCard α count) :=
      nodup.length_le_card
    _ = Nat.card (Set.powersetCard α count) :=
      Fintype.card_eq_nat_card
    _ = Nat.choose (Nat.card α) count := Set.powersetCard.card α count
    _ = Nat.choose enumeration.card count := by
      rw [natCard_eq enumeration]

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

/-- Exact lexicographic enumeration of a dependent finite family.  The base
order is outermost and every fibre uses its declared local order. -/
@[implicit_reducible]
def sigma {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value)) :
    FinEnum (Σ value, β value) := by
  letI : FinEnum α := base
  letI (value : α) : FinEnum (β value) := fibre value
  exact inferInstance

/-- Cardinality of the dependent schedule is the sum of its declared fibre
cardinalities. -/
theorem sigma_card {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value)) :
    (sigma base fibre).card = ∑ value, (fibre value).card := by
  letI : FinEnum α := base
  letI (value : α) : FinEnum (β value) := fibre value
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro value _member
  exact FinEnum.card_eq_fintypeCard.symm

/-- A uniform fibre cap gives the expected product bound without exposing
`Fintype.card_sigma` to applications. -/
theorem sigma_card_le_mul {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value))
    (cap : Nat) (bounded : ∀ value, (fibre value).card ≤ cap) :
    (sigma base fibre).card ≤ base.card * cap := by
  rw [sigma_card]
  letI : FinEnum α := base
  calc
    ∑ value, (fibre value).card ≤ ∑ _value : α, cap :=
      Finset.sum_le_sum fun value _member => bounded value
    _ = Fintype.card α * cap := by simp
    _ = base.card * cap := by rw [FinEnum.card_eq_fintypeCard]

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

/-- The size of a restricted enumeration is exactly the number of accepted
values in the supplied source enumeration.  This is the canonical bridge from
an application predicate to its locally owned `FinEnum` subtype; consumers do
not need to expose `Fintype.card_subtype` or rebuild instance plumbing. -/
theorem subtype_card_eq_filter {α : Type u} (enumeration : FinEnum α)
    (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    (subtype enumeration predicate decidePredicate).card =
      ((@Finset.univ α (@FinEnum.instFintype α enumeration)).filter
        predicate).card := by
  letI : FinEnum α := enumeration
  letI : DecidablePred predicate := decidePredicate
  letI : FinEnum {value // predicate value} :=
    subtype enumeration predicate decidePredicate
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]

/-- Exact cardinality of a predicate-selected Boolean fibre.  Tiny Boolean
response columns occur throughout graph CTs; this bridge keeps their local
two-entry accounting independent of subtype and decidability instances. -/
theorem boolSubtype_card (predicate : Bool → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    (subtype bool predicate decidePredicate).card =
      (if predicate false then 1 else 0) +
        (if predicate true then 1 else 0) := by
  rw [subtype_card_eq_filter]
  letI : DecidablePred predicate := decidePredicate
  rw [show (@Finset.univ Bool (@FinEnum.instFintype Bool bool)) =
      {false, true} by decide]
  by_cases atFalse : predicate false <;>
    by_cases atTrue : predicate true
  all_goals
    rw [Finset.filter_insert, Finset.filter_singleton]
    simp [atFalse, atTrue]

/-- Restrict an exact enumeration to the elements owned by a `Finset`.

This is the canonical framework representation of a finite local carrier:
applications supply the owning `Finset`, while the framework supplies the
subtype enumeration and its instance plumbing. -/
@[implicit_reducible]
def finsetSubtype {α : Type u} (enumeration : FinEnum α)
    (selected : Finset α) : FinEnum {value // value ∈ selected} :=
  subtype enumeration (fun value => value ∈ selected) (fun _value => by
    letI : DecidableEq α := enumeration.decEq
    infer_instance)

/-- Restricting an exact enumeration to an owning `Finset` has exactly the
cardinality of that `Finset`. -/
theorem finsetSubtype_card {α : Type u} (enumeration : FinEnum α)
    (selected : Finset α) :
    (finsetSubtype enumeration selected).card = selected.card := by
  letI : DecidableEq α := enumeration.decEq
  rw [finsetSubtype, subtype_card_eq_filter]
  simp

/-- The universe induced by `finsetSubtype` is exactly the attached owning
`Finset`, independently of which `Fintype` instance Lean would otherwise
choose for the subtype. -/
theorem finsetSubtype_univ_eq_attach {α : Type u}
    (enumeration : FinEnum α) (selected : Finset α) :
    @Finset.univ {value // value ∈ selected}
        (@FinEnum.instFintype _ (finsetSubtype enumeration selected)) =
      selected.attach := by
  apply Finset.Subset.antisymm
  · intro value _member
    exact Finset.mem_attach selected value
  · intro value _member
    exact @Finset.mem_univ {value // value ∈ selected}
      (@FinEnum.instFintype _ (finsetSubtype enumeration selected)) value

/-- Big-operator bridge for a locally owned finite carrier.  Consumers can
enumerate through `FinEnum` and prove their mathematical identity as a sum
over the original owning `Finset`, without repeating typeclass conversions. -/
theorem finsetSubtype_sum_eq_attach {α : Type u} {M : Type v}
    [AddCommMonoid M] (enumeration : FinEnum α) (selected : Finset α)
    (weight : {value // value ∈ selected} → M) :
    (@Finset.univ {value // value ∈ selected}
        (@FinEnum.instFintype _ (finsetSubtype enumeration selected))).sum weight =
      selected.attach.sum weight := by
  rw [finsetSubtype_univ_eq_attach]

/-- Direct big-operator bridge for weights depending only on the underlying
value.  It combines the subtype-universe and `Finset.attach` conversions so
applications can state their mathematical sum on the owning `Finset`. -/
theorem finsetSubtype_sum_val_eq {α : Type u} {M : Type v}
    [AddCommMonoid M] (enumeration : FinEnum α) (selected : Finset α)
    (weight : α → M) :
    (@Finset.univ {value // value ∈ selected}
        (@FinEnum.instFintype _ (finsetSubtype enumeration selected))).sum
        (fun value => weight value.1) =
      selected.sum weight := by
  rw [finsetSubtype_univ_eq_attach]
  exact Finset.sum_attach selected weight

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

/-- Dependent schedule consisting of one base item and one canonical pair
from that item's local fibre. -/
@[implicit_reducible]
def sigmaOrderedDistinctPairs {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value)) :
    FinEnum (Σ value, OrderedDistinctPair (fibre value)) :=
  sigma base (fun value => orderedDistinctPairs (fibre value))

/-- Exact size of a dependent canonical-pair schedule. -/
theorem sigmaOrderedDistinctPairs_card {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value)) :
    (sigmaOrderedDistinctPairs base fibre).card =
      ∑ value, Nat.choose (fibre value).card 2 := by
  rw [sigma_card]
  apply Finset.sum_congr rfl
  intro value _member
  exact orderedDistinctPairs_card (fibre value)

/-- A uniform local-fibre bound gives a quadratic-per-base bound for the
dependent canonical-pair schedule. -/
theorem sigmaOrderedDistinctPairs_card_le_mul_square
    {α : Type u} {β : α → Type v}
    (base : FinEnum α) (fibre : ∀ value, FinEnum (β value))
    (cap : Nat) (bounded : ∀ value, (fibre value).card ≤ cap) :
    (sigmaOrderedDistinctPairs base fibre).card ≤ base.card * cap ^ 2 := by
  apply sigma_card_le_mul base
    (fun value => orderedDistinctPairs (fibre value)) (cap ^ 2)
  intro value
  exact (orderedDistinctPairs_card_le_square (fibre value)).trans
    (Nat.pow_le_pow_left (bounded value) 2)

/-- Exact ordered enumeration of all lists of length at most `bound`. -/
@[implicit_reducible]
def boundedList {α : Type u} (enumeration : FinEnum α)
    (bound : Nat) : FinEnum (BoundedList α bound) :=
  @FinEnum.ofNodupList (BoundedList α bound)
    (letI : DecidableEq α := enumeration.decEq; inferInstance)
    (BoundedList.elems enumeration.orderedValues bound)
    (BoundedList.mem_elems enumeration)
    (BoundedList.elems_nodup enumeration.nodup_orderedValues bound)

/-- The positive tail of `finRange` retains its canonical index value.  This
small generic lemma prevents dependent applications from unfolding their
entire stage carrier while rewriting `getElem_drop`. -/
theorem finRange_drop_one_getElem_val (bound index : Nat)
    (inBounds : index < ((List.finRange bound).drop 1).length) :
    ((List.finRange bound).drop 1)[index].val = index + 1 := by
  rw [List.getElem_drop, List.getElem_finRange]
  simp only [Fin.val_cast]
  omega

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
