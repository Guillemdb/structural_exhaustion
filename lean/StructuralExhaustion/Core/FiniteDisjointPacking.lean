import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Powerset
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.FiniteDisjointPacking

universe uVertex uItem

/-!
# Finite disjoint packings

This file contains the domain-independent mathematics behind packing stages.
Items are represented only through finite vertex supports.  A maximum packing
is selected by finite choice, so no executable routine materializes the
finite universe of items or the powerset of possible packings.  Subsequent
machines consume only the selected packing.
-/

/-- Static data for a finite family of nonempty vertex supports.  The
representative is used to bound every pairwise-disjoint packing by the number
of host vertices. -/
structure Profile (Vertex : Type uVertex) (Item : Type uItem) where
  vertices : FinEnum Vertex
  finiteItems : Finite Item
  support : Item → Finset Vertex
  representative : Item → Vertex
  representative_mem : ∀ item, representative item ∈ support item

namespace Profile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (profile : Profile Vertex Item)

/-- Pairwise vertex-disjointness of a finite item family. -/
def IsPacking (items : Finset Item) : Prop :=
  (items : Set Item).PairwiseDisjoint profile.support

/-- A finite family together with its exact disjointness proof. -/
abbrev Packing := {items : Finset Item // profile.IsPacking items}

noncomputable instance packingFinite : Finite profile.Packing := by
  letI : Finite Item := profile.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : Fintype (Finset Item) := Finset.fintype
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance packingNonempty : Nonempty profile.Packing := by
  classical
  exact ⟨∅, by simp [IsPacking]⟩

/-- A maximum-cardinality pairwise-disjoint family exists for every finite
item type.  This is a proof-level finite maximum, not an enumeration routine. -/
theorem exists_maximum :
    ∃ packing : profile.Packing,
      ∀ other : profile.Packing, other.1.card ≤ packing.1.card :=
  Finite.exists_max fun packing : profile.Packing => packing.1.card

/-- One proof-selected maximum packing. -/
noncomputable def maximum : profile.Packing :=
  Classical.choose profile.exists_maximum

/-- The selected packing has maximum cardinality among all disjoint
families. -/
theorem maximum_spec (other : profile.Packing) :
    other.1.card ≤ profile.maximum.1.card :=
  Classical.choose_spec profile.exists_maximum other

/-- Maximum cardinality implies maximality: every item intersects a selected
support. -/
theorem maximum_saturated (item : Item) :
    ∃ selected ∈ profile.maximum.1,
      ¬Disjoint (profile.support item) (profile.support selected) := by
  classical
  by_contra noIntersection
  have disjointFromAll :
      ∀ selected ∈ profile.maximum.1,
        Disjoint (profile.support item) (profile.support selected) := by
    intro selected selectedMem
    by_contra intersects
    exact noIntersection ⟨selected, selectedMem, intersects⟩
  have itemNotMem : item ∉ profile.maximum.1 := by
    intro itemMem
    have selfDisjoint := disjointFromAll item itemMem
    exact (Finset.disjoint_left.mp selfDisjoint
      (profile.representative_mem item)) (profile.representative_mem item)
  let extended : profile.Packing :=
    ⟨insert item profile.maximum.1, by
      change ((insert item profile.maximum.1 : Finset Item) : Set Item).PairwiseDisjoint
        profile.support
      rw [Finset.coe_insert,
        Set.pairwiseDisjoint_insert_of_notMem (by simpa using itemNotMem)]
      exact ⟨profile.maximum.2, disjointFromAll⟩⟩
  have impossible := profile.maximum_spec extended
  simp [extended, itemNotMem] at impossible
  omega

/-- The list consumed by local peeling machines.  It contains exactly the
selected maximum packing and no duplicates. -/
noncomputable def values : List Item := profile.maximum.1.toList

theorem values_nodup : profile.values.Nodup :=
  profile.maximum.1.nodup_toList

theorem mem_values_iff (item : Item) :
    item ∈ profile.values ↔ item ∈ profile.maximum.1 :=
  Finset.mem_toList

theorem values_length :
    profile.values.length = profile.maximum.1.card :=
  Finset.length_toList profile.maximum.1

theorem values_pairwise :
    profile.values.Pairwise
      (Function.onFun Disjoint profile.support) := by
  classical
  rw [← List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
    profile.values_nodup]
  simpa [values, Finset.toList_toFinset, IsPacking] using
    profile.maximum.2

/-- Every other duplicate-free pairwise-disjoint list is no longer than the
selected list. -/
theorem list_length_le_values (other : List Item)
    (nodup : other.Nodup)
    (pairwise : other.Pairwise (Function.onFun Disjoint profile.support)) :
    other.length ≤ profile.values.length := by
  classical
  let packing : profile.Packing :=
    ⟨other.toFinset, by
      exact (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        nodup).2 pairwise⟩
  rw [profile.values_length, ← List.toFinset_card_of_nodup nodup]
  exact profile.maximum_spec packing

/-- The selected list is saturated: every unselected item meets one of its
members. -/
theorem values_saturated (item : Item) :
    ∃ selected ∈ profile.values,
      ¬Disjoint (profile.support item) (profile.support selected) := by
  rcases profile.maximum_saturated item with
    ⟨selected, selectedMem, intersects⟩
  exact ⟨selected, (profile.mem_values_iff selected).2 selectedMem,
    intersects⟩

/-- Disjoint nonempty supports admit an injective representative map into
the host vertices. -/
theorem packing_card_le_vertices (packing : profile.Packing) :
    packing.1.card ≤ profile.vertices.card := by
  letI : FinEnum Vertex := profile.vertices
  let representative : packing.1 → Vertex := fun item =>
    profile.representative item.1
  have injective : Function.Injective representative := by
    intro left right representativesEqual
    apply Subtype.ext
    by_contra itemsDifferent
    have supportsDisjoint :
        Disjoint (profile.support left.1) (profile.support right.1) :=
      packing.2 left.2 right.2 itemsDifferent
    have leftMem := profile.representative_mem left.1
    have rightMem := profile.representative_mem right.1
    change profile.representative left.1 =
      profile.representative right.1 at representativesEqual
    rw [representativesEqual] at leftMem
    exact (Finset.disjoint_left.mp supportsDisjoint leftMem) rightMem
  simpa [Fintype.card_coe, FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective representative injective

/-- The maximum list has at most one peeling iteration per host vertex. -/
theorem values_length_le_vertices :
    profile.values.length ≤ profile.vertices.card := by
  rw [profile.values_length]
  exact profile.packing_card_le_vertices profile.maximum

/-- If at least one item exists, then the maximum packing is nonempty. -/
theorem values_nonempty_of_item (item : Item) : profile.values ≠ [] := by
  rcases profile.values_saturated item with ⟨selected, selectedMem, _⟩
  exact List.ne_nil_of_mem selectedMem

end Profile

end StructuralExhaustion.Core.FiniteDisjointPacking
