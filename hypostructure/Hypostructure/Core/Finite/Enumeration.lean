import Hypostructure.Core.Prelude

/-!
# Exact finite schedules

An `Enumeration` is an explicit deterministic schedule for the exact finite
family owned by a residual.  It does not claim that the ambient type is
finite.  `CompleteEnumeration` adds that stronger claim when a caller really
does supply every inhabitant.

Order is proof-relevant execution metadata: first-hit scans consume `values`
from left to right.  Set-like reasoning is delegated to Mathlib's `List` and
`Finset` APIs.
-/

namespace Hypostructure.Core.Finite

universe u v

/-- An explicit, duplicate-free, deterministic finite schedule. -/
structure Enumeration (α : Type u) where
  values : List α
  nodup : values.Nodup
  decEq : DecidableEq α

namespace Enumeration

/-- Build a schedule from the exact ordered list supplied by a residual. -/
def ofNodupList {α : Type u} [DecidableEq α]
    (values : List α) (nodup : values.Nodup) : Enumeration α where
  values := values
  nodup := nodup
  decEq := inferInstance

/-- The empty exact family. -/
def empty (α : Type u) [DecidableEq α] : Enumeration α :=
  ofNodupList [] (by simp)

/-- A one-member exact family. -/
def singleton {α : Type u} [DecidableEq α] (value : α) : Enumeration α :=
  ofNodupList [value] (by simp)

/-- Number of scheduled members. -/
def card {α : Type u} (schedule : Enumeration α) : Nat :=
  schedule.values.length

/-- Retrieve the member at an exact schedule index. -/
def get {α : Type u} (schedule : Enumeration α)
    (index : Fin schedule.card) : α :=
  schedule.values.get index

@[simp] theorem card_eq_length {α : Type u} (schedule : Enumeration α) :
    schedule.card = schedule.values.length :=
  rfl

theorem get_mem {α : Type u} (schedule : Enumeration α)
    (index : Fin schedule.card) : schedule.get index ∈ schedule.values :=
  List.get_mem _ _

/-- Membership is equivalent to occurrence at an exact schedule index. -/
theorem mem_iff_exists_index {α : Type u} (schedule : Enumeration α)
    (value : α) :
    value ∈ schedule.values ↔
      ∃ index : Fin schedule.card, schedule.get index = value := by
  simpa [card, get] using
    (List.mem_iff_get (l := schedule.values) (a := value))

/-- Duplicate freedom makes the schedule index of a member unique. -/
theorem unique_index {α : Type u} (schedule : Enumeration α)
    {left right : Fin schedule.card}
    (equal : schedule.get left = schedule.get right) : left = right :=
  schedule.nodup.injective_get equal

/-- Forget order explicitly when a `Finset` is the appropriate interface. -/
def toFinset {α : Type u} (schedule : Enumeration α) : Finset α :=
  @List.toFinset α schedule.decEq schedule.values

@[simp] theorem mem_toFinset {α : Type u} (schedule : Enumeration α)
    (value : α) : value ∈ schedule.toFinset ↔ value ∈ schedule.values := by
  letI : DecidableEq α := schedule.decEq
  simp [toFinset]

@[simp] theorem card_toFinset {α : Type u} (schedule : Enumeration α) :
    schedule.toFinset.card = schedule.card := by
  letI : DecidableEq α := schedule.decEq
  simpa [toFinset, card] using List.toFinset_card_of_nodup schedule.nodup

/-- Turn a `Finset` into a deterministic schedule using its canonical sorted
order.  Requiring `LinearOrder` makes the tie-breaking order explicit. -/
def ofFinset {α : Type u} [LinearOrder α]
    (members : Finset α) : Enumeration α where
  values := members.sort (· ≤ ·)
  nodup := members.sort_nodup (· ≤ ·)
  decEq := inferInstance

@[simp] theorem mem_ofFinset_values {α : Type u} [LinearOrder α]
    (members : Finset α) (value : α) :
    value ∈ (ofFinset members).values ↔ value ∈ members := by
  simp [ofFinset]

@[simp] theorem toFinset_ofFinset {α : Type u} [LinearOrder α]
    (members : Finset α) : (ofFinset members).toFinset = members := by
  simp [toFinset, ofFinset]

/-- Use an explicit Mathlib `FinEnum` value without relying on global
typeclass inference for the schedule or its order. -/
def ofFinEnum {α : Type u} (enumeration : FinEnum α) : Enumeration α where
  values := @FinEnum.toList α enumeration
  nodup := @FinEnum.nodup_toList α enumeration
  decEq := enumeration.decEq

@[simp] theorem mem_ofFinEnum_values {α : Type u}
    (enumeration : FinEnum α) (value : α) :
    value ∈ (ofFinEnum enumeration).values :=
  @FinEnum.mem_toList α enumeration value

@[simp] theorem card_ofFinEnum {α : Type u}
    (enumeration : FinEnum α) :
    (ofFinEnum enumeration).card = enumeration.card := by
  simp [ofFinEnum, card, FinEnum.toList]

/-- Apply an injective representation change while retaining exact order. -/
def map {α : Type u} {β : Type v} (schedule : Enumeration α)
    (f : α -> β) (injective : Function.Injective f)
    (decEq : DecidableEq β) : Enumeration β where
  values := schedule.values.map f
  nodup := schedule.nodup.map injective
  decEq := decEq

@[simp] theorem mem_map_values {α : Type u} {β : Type v}
    (schedule : Enumeration α) (f : α -> β)
    (injective : Function.Injective f) (decEq : DecidableEq β)
    (value : β) :
    value ∈ (schedule.map f injective decEq).values ↔
      ∃ source ∈ schedule.values, f source = value := by
  simp [map]

/-- Lexicographic product: the right schedule is exhausted for each left
member before the next left member is inspected. -/
def product {α : Type u} {β : Type v}
    (left : Enumeration α) (right : Enumeration β) :
    Enumeration (α × β) where
  values := left.values ×ˢ right.values
  nodup := left.nodup.product right.nodup
  decEq := by
    letI : DecidableEq α := left.decEq
    letI : DecidableEq β := right.decEq
    exact inferInstance

@[simp] theorem mem_product_values {α : Type u} {β : Type v}
    (left : Enumeration α) (right : Enumeration β) (value : α × β) :
    value ∈ (left.product right).values ↔
      value.1 ∈ left.values ∧ value.2 ∈ right.values := by
  simpa [product] using
    (List.mem_product (l₁ := left.values) (l₂ := right.values)
      (a := value.1) (b := value.2))

@[simp] theorem card_product {α : Type u} {β : Type v}
    (left : Enumeration α) (right : Enumeration β) :
    (left.product right).card = left.card * right.card := by
  simp [product, card, List.length_product]

private def subtypeCandidate {α : Type u} (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (value : α) : Option {value // predicate value} :=
  if proof : predicate value then some ⟨value, proof⟩ else none

/-- Restrict an explicit schedule to the members satisfying a decidable
predicate, retaining their original relative order. -/
def subtype {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    Enumeration {value // predicate value} where
  values := schedule.values.filterMap
    (subtypeCandidate predicate decidePredicate)
  nodup := schedule.nodup.filterMap (by
    intro left right value leftMem rightMem
    simp only [subtypeCandidate] at leftMem rightMem
    split at leftMem <;> simp_all
    exact congrArg Subtype.val leftMem)
  decEq := by
    letI : DecidableEq α := schedule.decEq
    exact inferInstance

@[simp] theorem mem_subtype_values {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (value : {value // predicate value}) :
    value ∈ (schedule.subtype predicate decidePredicate).values ↔
      value.1 ∈ schedule.values := by
  simp [subtype, subtypeCandidate]

end Enumeration

/-- A complete schedule additionally proves that every ambient inhabitant is
one of its explicit members. -/
structure CompleteEnumeration (α : Type u) extends Enumeration α where
  complete : forall value : α, value ∈ values

namespace CompleteEnumeration

/-- An explicit `FinEnum` supplies a complete deterministic schedule. -/
def ofFinEnum {α : Type u} (enumeration : FinEnum α) :
    CompleteEnumeration α where
  toEnumeration := Enumeration.ofFinEnum enumeration
  complete := Enumeration.mem_ofFinEnum_values enumeration

/-- Product completeness is derived from the two supplied schedules. -/
def product {α : Type u} {β : Type v}
    (left : CompleteEnumeration α) (right : CompleteEnumeration β) :
    CompleteEnumeration (α × β) where
  toEnumeration := left.toEnumeration.product right.toEnumeration
  complete := by
    intro value
    simp [left.complete value.1, right.complete value.2]

/-- Filtering a complete ambient schedule gives a complete schedule for the
corresponding subtype, without enumerating anything outside the input. -/
def subtype {α : Type u} (schedule : CompleteEnumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    CompleteEnumeration {value // predicate value} where
  toEnumeration := schedule.toEnumeration.subtype predicate decidePredicate
  complete := by
    intro value
    simpa using schedule.complete value.1

end CompleteEnumeration

/-- Explicit schedules for a dependent finite family. -/
structure DependentEnumeration (index : Type u)
    (fibre : index -> Type v) where
  indices : Enumeration index
  fibres : (i : index) -> Enumeration (fibre i)

namespace DependentEnumeration

/-- Flatten a dependent schedule in index-major order. -/
def flatten {index : Type u} {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre) :
    Enumeration (Sigma fibre) where
  values := schedule.indices.values.sigma
    (fun i => (schedule.fibres i).values)
  nodup := schedule.indices.nodup.sigma
    (fun i => (schedule.fibres i).nodup)
  decEq := by
    letI : DecidableEq index := schedule.indices.decEq
    letI (i : index) : DecidableEq (fibre i) :=
      (schedule.fibres i).decEq
    exact inferInstance

@[simp] theorem mem_flatten_values {index : Type u}
    {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre)
    (value : Sigma fibre) :
    value ∈ schedule.flatten.values ↔
      value.1 ∈ schedule.indices.values ∧
        value.2 ∈ (schedule.fibres value.1).values := by
  simpa [flatten] using
    (List.mem_sigma (l₁ := schedule.indices.values)
      (l₂ := fun i => (schedule.fibres i).values)
      (a := value.1) (b := value.2))

@[simp] theorem card_flatten {index : Type u}
    {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre) :
    schedule.flatten.card =
      (schedule.indices.values.map fun i => (schedule.fibres i).card).sum := by
  simp [flatten, Enumeration.card, List.length_sigma]

end DependentEnumeration

end Hypostructure.Core.Finite
