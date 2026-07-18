import StructuralExhaustion.Core.BoundedListCode

namespace StructuralExhaustion.Core.FiniteObservedColumn

universe u

/-!
# Finite observed columns

This module packages the recurring structural-exhaustion pattern in which a
proof stage observes a duplicate-free list from a fixed finite alphabet.  The
framework chooses the alphabet cardinality as the list bound, pads the list to
a symbolic function code, and carries the exact `Fin` encoding.  Clients never
construct or enumerate the space of columns.
-/

/-- Framework-owned metadata for one finite observed column. -/
structure Encoding (α : Type u) where
  alphabetCard : Nat
  alphabetEquiv : α ≃ Fin alphabetCard

namespace Encoding

/-- The canonical column package for a finite alphabet. -/
noncomputable def ofFintype (α : Type u) [Fintype α] : Encoding α where
  alphabetCard := Fintype.card α
  alphabetEquiv := Fintype.equivFin α

/-- A column stores at most one occurrence of each alphabet value. -/
abbrev Bound {α : Type u} (encoding : Encoding α) := encoding.alphabetCard

/-- Symbolically padded column code. -/
abbrev Code {α : Type u} (encoding : Encoding α) :=
  BoundedListCode.Code α encoding.Bound

/-- Exact symbolic cardinality of the padded column-code space. -/
def codeCard {α : Type u} (encoding : Encoding α) : Nat :=
  (encoding.alphabetCard + 1) ^ encoding.Bound

/-- The exact symbolic encoder; constructing it does not enumerate columns. -/
noncomputable def codeEquivFin {α : Type u} (encoding : Encoding α) :
    encoding.Code ≃ Fin encoding.codeCard :=
  BoundedListCode.codeEquivFinOfEquiv
    encoding.alphabetEquiv encoding.Bound

/-- Encode one actually observed duplicate-free list. -/
def encodeNodup {α : Type u} [Fintype α] (encoding : Encoding α)
    (values : List α) (nodup : values.Nodup) : encoding.Code :=
  BoundedListCode.encode ⟨values, nodup.length_le_card.trans_eq (by
    simpa using Fintype.card_congr encoding.alphabetEquiv)⟩

theorem codeEquivFin_injective {α : Type u} (encoding : Encoding α) :
    Function.Injective encoding.codeEquivFin :=
  encoding.codeEquivFin.injective

end Encoding

/-- The recurring four observed columns carried by a structural cut state.
Applications choose only the four alphabets; the framework owns all bounds,
codes, encoders, and their combined cardinality. -/
structure FourEncoding (D4 D5 D6 D7 : Type*) where
  d4 : Encoding D4
  d5 : Encoding D5
  d6 : Encoding D6
  d7 : Encoding D7

namespace FourEncoding

/-- Canonical four-column package for finite alphabets. -/
noncomputable def ofFintype
    (D4 D5 D6 D7 : Type*)
    [Fintype D4] [Fintype D5] [Fintype D6] [Fintype D7] :
    FourEncoding D4 D5 D6 D7 where
  d4 := Encoding.ofFintype D4
  d5 := Encoding.ofFintype D5
  d6 := Encoding.ofFintype D6
  d7 := Encoding.ofFintype D7

/-- The exact symbolic `Q_cols` factor.  It is computed from the four column
packages and therefore never restated by an application. -/
def qCols {D4 D5 D6 D7 : Type*} (columns : FourEncoding D4 D5 D6 D7) : Nat :=
  columns.d4.codeCard * columns.d5.codeCard *
    columns.d6.codeCard * columns.d7.codeCard

end FourEncoding

end StructuralExhaustion.Core.FiniteObservedColumn
