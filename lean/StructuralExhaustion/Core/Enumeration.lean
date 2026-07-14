import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.FinEnum

namespace StructuralExhaustion.Core

universe u v

/-!
Exact, ordered finite enumerations used by the reference runners.

Total universes are represented directly by explicit Mathlib `FinEnum` values.
Keeping the enumerator as a value, rather than relying on global typeclass
search, lets two machines use different deterministic orders on the same
finite type.  The derived list order is part of the reference semantics.
-/

/-- A finite ordered collection, without the claim that it contains every
inhabitant of its element type.

This is intentionally a duplicate-free list rather than a `Finset`: first-hit
machine semantics consume its order.  All set-like reasoning should pass
through Mathlib's `List`/`Finset` API instead of adding another collection
implementation here. -/
structure OrderedCollection (α : Type u) where
  values : List α
  nodup : values.Nodup
  decEq : DecidableEq α

/-- An exact enumeration of a dependent family over an exact finite index
universe. -/
structure DependentEnumeration (ι : Type u) (α : ι → Type v) where
  indices : FinEnum ι
  fibres : (i : ι) → FinEnum (α i)

namespace OrderedCollection

/-- The unordered Mathlib view used for set-like membership/cardinality
reasoning.  Conversion is explicit so machine code cannot accidentally forget
that `values` also carries scheduling order. -/
def toFinset {α : Type u} (collection : OrderedCollection α) : Finset α :=
  @List.toFinset α collection.decEq collection.values

@[simp]
theorem mem_toFinset {α : Type u} (collection : OrderedCollection α)
    (value : α) : value ∈ collection.toFinset ↔ value ∈ collection.values := by
  letI : DecidableEq α := collection.decEq
  simp [toFinset]

/-- Summing in the observable duplicate-free list order agrees with summing
over the unordered Mathlib finset view. -/
theorem sum_values_eq_sum_toFinset {α : Type u} {M : Type v}
    [AddCommMonoid M] (collection : OrderedCollection α) (f : α → M) :
    (collection.values.map f).sum = ∑ value ∈ collection.toFinset, f value := by
  letI : DecidableEq α := collection.decEq
  have aux : ∀ values : List α, values.Nodup →
      (values.map f).sum = ∑ value ∈ values.toFinset, f value := by
    intro values nodup
    induction values with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
        rw [Finset.sum_insert (by
          simpa using (List.nodup_cons.mp nodup).1),
          ih (List.nodup_cons.mp nodup).2]
  exact aux collection.values collection.nodup

end OrderedCollection

end StructuralExhaustion.Core

namespace FinEnum

/-- The deterministic list exposed by an explicit Mathlib enumeration value. -/
def orderedValues {α : Type u} (enumeration : FinEnum α) : List α :=
  @FinEnum.toList α enumeration

/-- The observable list has exactly the cardinality recorded by its explicit
enumeration. -/
@[simp] theorem orderedValues_length {α : Type u}
    (enumeration : FinEnum α) :
    enumeration.orderedValues.length = enumeration.card := by
  simp [orderedValues, FinEnum.toList]

/-- The exposed enumeration contains no duplicate. -/
theorem nodup_orderedValues {α : Type u} (enumeration : FinEnum α) :
    enumeration.orderedValues.Nodup :=
  @FinEnum.nodup_toList α enumeration

/-- Every inhabitant occurs in the exposed enumeration. -/
@[simp]
theorem mem_orderedValues {α : Type u} (enumeration : FinEnum α)
    (x : α) : x ∈ enumeration.orderedValues :=
  @FinEnum.mem_toList α enumeration x

/-- Forget universe completeness while retaining exact list membership. -/
def toOrderedCollection {α : Type u} (enumeration : FinEnum α) :
    StructuralExhaustion.Core.OrderedCollection α where
  values := enumeration.orderedValues
  nodup := enumeration.nodup_orderedValues
  decEq := enumeration.decEq

/-- The deterministic list sum exposed by a `FinEnum` is the standard
Mathlib `Fintype` sum. -/
theorem sum_orderedValues {α : Type u} {M : Type v} [AddCommMonoid M]
    (enumeration : FinEnum α) (f : α → M) :
    (enumeration.orderedValues.map f).sum = ∑ value : α, f value := by
  letI : FinEnum α := enumeration
  letI : DecidableEq α := enumeration.decEq
  change (enumeration.toOrderedCollection.values.map f).sum =
    ∑ value : α, f value
  rw [StructuralExhaustion.Core.OrderedCollection.sum_values_eq_sum_toFinset
    enumeration.toOrderedCollection f]
  apply Finset.sum_subset
  · intro value _member
    simp
  · intro value _univMember notMember
    exact (notMember (by simp [toOrderedCollection])).elim

end FinEnum

namespace StructuralExhaustion.Core.Enumeration

/-- Lift an exact enumeration to a chosen universe without changing its
observable order. -/
@[implicit_reducible]
def ulift {α : Type u} (enumeration : FinEnum α) : FinEnum (ULift.{v, u} α) :=
  FinEnum.ofNodupList
    (enumeration.orderedValues.map ULift.up)
    (by
      intro value
      rcases value with ⟨value⟩
      simp)
    (enumeration.nodup_orderedValues.map (by
      intro left right equal
      exact congrArg ULift.down equal))

theorem ulift_card {α : Type u} (enumeration : FinEnum α) :
    (@ulift.{u, v} α enumeration).card = enumeration.card := by
  letI : FinEnum α := enumeration
  letI : FinEnum (ULift.{v, u} α) := ulift enumeration
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard,
    Fintype.card_ulift]

/-- Canonical explicit enumeration of the empty type. -/
@[implicit_reducible]
def empty : FinEnum Empty :=
  @FinEnum.ofNodupList Empty inferInstance []
    (by intro value; nomatch value) (by simp)

/-- Canonical explicit enumeration of `Unit`. -/
@[implicit_reducible]
def unit : FinEnum Unit :=
  @FinEnum.ofNodupList Unit inferInstance [()]
    (by intro value; cases value; simp) (by simp)

/-- Canonical false-before-true enumeration of `Bool`. -/
@[implicit_reducible]
def bool : FinEnum Bool :=
  @FinEnum.ofNodupList Bool inferInstance [false, true]
    (by intro value; cases value <;> simp) (by decide)

end StructuralExhaustion.Core.Enumeration
