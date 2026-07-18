import StructuralExhaustion.Core.FiniteDisjointPacking
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteBoundedOverlap

open StructuralExhaustion

universe uVertex uItem

/-!
# Finite bounded-overlap extraction

This profile is the reusable counting layer behind local-support extraction.
It consumes an explicitly finite family of nonempty supports and a uniform
bound on the number of supplied supports meeting any one supplied support.
The selected family is the proof-level maximum disjoint packing from
`FiniteDisjointPacking`; no family of ambient graphs or recursively generated
supports is enumerated.
-/

structure Profile (Vertex : Type uVertex) (Item : Type uItem) where
  packing : Core.FiniteDisjointPacking.Profile Vertex Item
  overlapBound : Nat
  overlap_bounded : ∀ selected : Item,
    letI : Finite Item := packing.finiteItems
    letI : Fintype Item := Fintype.ofFinite Item
    letI : DecidableEq Vertex := packing.vertices.decEq
    ((Finset.univ : Finset Item).filter fun item =>
      ¬Disjoint (packing.support item) (packing.support selected)).card ≤
        overlapBound

/-- A local way to establish bounded overlap.  Every supplied support has at
most `supportSizeBound` vertices and every host vertex belongs to at most
`pointMultiplicityBound` supplied supports.  This is the form produced by
bounded-radius graph arguments; it avoids proving one overlap-fibre estimate
separately for every item. -/
structure LocalMultiplicityProfile (Vertex : Type uVertex) (Item : Type uItem) where
  packing : Core.FiniteDisjointPacking.Profile Vertex Item
  supportSizeBound : Nat
  pointMultiplicityBound : Nat
  support_card_le : ∀ item,
    (packing.support item).card ≤ supportSizeBound
  point_multiplicity_bounded : ∀ vertex,
    letI : Finite Item := packing.finiteItems
    letI : Fintype Item := Fintype.ofFinite Item
    letI : DecidableEq Vertex := packing.vertices.decEq
    ((Finset.univ : Finset Item).filter fun item =>
      vertex ∈ packing.support item).card ≤ pointMultiplicityBound

namespace LocalMultiplicityProfile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (bounds : LocalMultiplicityProfile Vertex Item)

/-- All supplied supports containing one fixed host vertex. -/
noncomputable def pointFibre (vertex : Vertex) : Finset Item := by
  letI : Finite Item := bounds.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Vertex := bounds.packing.vertices.decEq
  exact (Finset.univ : Finset Item).filter fun item =>
    vertex ∈ bounds.packing.support item

theorem pointFibre_card_le (vertex : Vertex) :
    (bounds.pointFibre vertex).card ≤ bounds.pointMultiplicityBound := by
  simpa [pointFibre] using bounds.point_multiplicity_bounded vertex

/-- All supplied supports meeting one fixed support. -/
noncomputable def overlapFibre (selected : Item) : Finset Item := by
  letI : Finite Item := bounds.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Vertex := bounds.packing.vertices.decEq
  exact (Finset.univ : Finset Item).filter fun item =>
    ¬Disjoint (bounds.packing.support item) (bounds.packing.support selected)

theorem mem_overlapFibre_iff (selected item : Item) :
    item ∈ bounds.overlapFibre selected ↔
      ¬Disjoint (bounds.packing.support item)
        (bounds.packing.support selected) := by
  letI : Finite Item := bounds.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Vertex := bounds.packing.vertices.decEq
  simp [overlapFibre]

/-- Union of the point fibres over one literal support. -/
noncomputable def pointFibreUnion (selected : Item) : Finset Item := by
  letI : Finite Item := bounds.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Item := Classical.decEq Item
  letI : DecidableEq Vertex := bounds.packing.vertices.decEq
  exact (bounds.packing.support selected).biUnion bounds.pointFibre

theorem mem_pointFibreUnion_of_mem (selected item : Item) (vertex : Vertex)
    (selectedMem : vertex ∈ bounds.packing.support selected)
    (itemMem : vertex ∈ bounds.packing.support item) :
    item ∈ bounds.pointFibreUnion selected := by
  letI : Finite Item := bounds.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Item := Classical.decEq Item
  letI : DecidableEq Vertex := bounds.packing.vertices.decEq
  rw [pointFibreUnion, Finset.mem_biUnion]
  refine ⟨vertex, selectedMem, ?_⟩
  simp [pointFibre, itemMem]

/-- Every support meeting `selected` is contained in the union of the point
fibres over the literal vertices of `selected`. -/
theorem overlap_subset_pointFibre_union (selected : Item) :
    bounds.overlapFibre selected ⊆
      bounds.pointFibreUnion selected := by
  intro item member
  have intersects : ¬Disjoint (bounds.packing.support item)
      (bounds.packing.support selected) :=
    (bounds.mem_overlapFibre_iff selected item).1 member
  rw [Finset.not_disjoint_iff] at intersects
  rcases intersects with ⟨vertex, itemMem, selectedMem⟩
  exact bounds.mem_pointFibreUnion_of_mem selected item vertex
    selectedMem itemMem

/-- Support size times point multiplicity bounds the complete overlap fibre,
including the selected support itself. -/
theorem overlap_card_le_mul (selected : Item) :
    (bounds.overlapFibre selected).card ≤
      bounds.supportSizeBound * bounds.pointMultiplicityBound := by
  classical
  let support := bounds.packing.support selected
  calc
    (bounds.overlapFibre selected).card ≤
        (bounds.pointFibreUnion selected).card :=
      Finset.card_le_card (bounds.overlap_subset_pointFibre_union selected)
    _ ≤ ∑ vertex ∈ support, (bounds.pointFibre vertex).card := by
      unfold pointFibreUnion
      simpa using (Finset.card_biUnion_le
        (s := support) (t := bounds.pointFibre))
    _ ≤ ∑ _vertex ∈ support, bounds.pointMultiplicityBound := by
      exact Finset.sum_le_sum fun vertex _ => bounds.pointFibre_card_le vertex
    _ = support.card * bounds.pointMultiplicityBound := by simp
    _ ≤ bounds.supportSizeBound * bounds.pointMultiplicityBound :=
      Nat.mul_le_mul_right _ (bounds.support_card_le selected)

/-- Convert local size and point-multiplicity bounds to the existing
bounded-overlap profile.  The extra one matches the conventional
`D = M * B + 1` ledger used when `M * B` is described as the number of other
intersecting supports. -/
noncomputable def toProfile : Profile Vertex Item where
  packing := bounds.packing
  overlapBound := bounds.supportSizeBound * bounds.pointMultiplicityBound + 1
  overlap_bounded := fun selected => by
    simpa only [overlapFibre] using
      (bounds.overlap_card_le_mul selected).trans (Nat.le_add_right _ _)

end LocalMultiplicityProfile

namespace Profile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (profile : Profile Vertex Item)

/-- The proof-selected pairwise-disjoint local-support family. -/
noncomputable def selected : Finset Item := profile.packing.maximum.1

/-- Cardinality of the explicitly finite local item type. -/
noncomputable def itemCount : Nat := by
  letI : Finite Item := profile.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  exact Fintype.card Item

/-- The complete finite local item universe fixed by `finiteItems`. -/
noncomputable def allItems : Finset Item := by
  letI : Finite Item := profile.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  exact Finset.univ

/-- All supplied local supports meeting one selected support. -/
noncomputable def overlapFibre (selected : Item) : Finset Item := by
  letI : Finite Item := profile.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Vertex := profile.packing.vertices.decEq
  exact (Finset.univ : Finset Item).filter fun item =>
    ¬Disjoint (profile.packing.support item) (profile.packing.support selected)

/-- Union of the overlap fibres of the selected disjoint family. -/
noncomputable def overlapCover : Finset Item := by
  letI : Finite Item := profile.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  letI : DecidableEq Item := Classical.decEq Item
  exact profile.selected.biUnion profile.overlapFibre

theorem overlapFibre_card_le (selected : Item) :
    (profile.overlapFibre selected).card ≤ profile.overlapBound := by
  simpa [overlapFibre] using profile.overlap_bounded selected

/-- Maximality of the selected packing makes its overlap fibres cover the
entire explicitly supplied item universe. -/
theorem univ_subset_biUnion_overlapFibre :
    profile.allItems ⊆
      profile.overlapCover := by
  classical
  intro item _
  rcases Core.FiniteDisjointPacking.Profile.maximum_saturated
      profile.packing item with
    ⟨selected, selectedMem, intersects⟩
  rw [overlapCover, Finset.mem_biUnion]
  exact ⟨selected, selectedMem, by simp [overlapFibre, intersects]⟩

/-- Exact bounded-overlap packing inequality.  If every overlap fibre has at
most `D` members, the whole local family has at most `D` times as many
members as the extracted disjoint family. -/
theorem card_le_selected_mul_overlapBound :
    profile.itemCount ≤ profile.selected.card * profile.overlapBound := by
  classical
  letI : Finite Item := profile.packing.finiteItems
  letI : Fintype Item := Fintype.ofFinite Item
  have sumBound : ∀ items : Finset Item,
      (∑ selected ∈ items, (profile.overlapFibre selected).card) ≤
        items.card * profile.overlapBound := by
    intro items
    induction items using Finset.induction with
    | empty => simp
    | @insert selected items notMem ih =>
        rw [Finset.sum_insert notMem, Finset.card_insert_of_notMem notMem]
        have fibreBound := profile.overlapFibre_card_le selected
        calc
          (profile.overlapFibre selected).card +
              ∑ selected ∈ items, (profile.overlapFibre selected).card ≤
              profile.overlapBound + items.card * profile.overlapBound :=
            Nat.add_le_add fibreBound ih
          _ = (items.card + 1) * profile.overlapBound := by
            simp [Nat.add_mul, Nat.add_comm]
  calc
    profile.itemCount = profile.allItems.card := by
      simp [itemCount, allItems]
    _ ≤ profile.overlapCover.card :=
      Finset.card_le_card
        (univ_subset_biUnion_overlapFibre profile)
    _ ≤ ∑ selected ∈ profile.selected,
        (profile.overlapFibre selected).card := by
      simpa [overlapCover] using
        (Finset.card_biUnion_le
          (s := profile.selected) (t := profile.overlapFibre))
    _ ≤ profile.selected.card * profile.overlapBound :=
      sumBound profile.selected

/-- Division form used by quantitative ledgers. -/
theorem card_div_overlapBound_le_selected :
    profile.itemCount / profile.overlapBound ≤ profile.selected.card := by
  letI : Finite Item := profile.packing.finiteItems
  by_cases zero : profile.overlapBound = 0
  · simp [zero]
  · exact Nat.div_le_of_le_mul
      (by simpa [Nat.mul_comm] using
        profile.card_le_selected_mul_overlapBound)

/-- Exact routed-loss form of bounded-overlap extraction.  `supply` is the
upstream demand count and `loss` is the number of occurrences already sent to
named side ledgers.  The application only proves that the remaining supply is
represented in the explicitly supplied item family; the framework transports
that fact through the overlap bound. -/
theorem supply_sub_loss_div_le_selected (supply loss : Nat)
    (remaining_le : supply - loss ≤ profile.itemCount) :
    (supply - loss) / profile.overlapBound ≤ profile.selected.card := by
  by_cases zero : profile.overlapBound = 0
  · simp [zero]
  · apply Nat.div_le_of_le_mul
    exact remaining_le.trans (by
      simpa [Nat.mul_comm] using profile.card_le_selected_mul_overlapBound)

/-- Multiplicative form of the same routed-loss ledger.  This is convenient
before an application normalizes its declared lower-order loss term. -/
theorem supply_le_selected_mul_add_loss (supply loss : Nat)
    (remaining_le : supply - loss ≤ profile.itemCount)
    (loss_le_supply : loss ≤ supply) :
    supply ≤ profile.selected.card * profile.overlapBound + loss := by
  have packed : supply - loss ≤
      profile.selected.card * profile.overlapBound :=
    remaining_le.trans profile.card_le_selected_mul_overlapBound
  omega

/-- The extracted supports are pairwise vertex-disjoint. -/
theorem selected_pairwise :
    (profile.selected : Set Item).PairwiseDisjoint profile.packing.support :=
  profile.packing.maximum.2

end Profile

namespace LocalMultiplicityProfile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (bounds : LocalMultiplicityProfile Vertex Item)

/-- Division-form extraction with the paper's `M * B + 1` denominator. -/
theorem extracted_div_bound :
    (bounds.toProfile.itemCount /
      (bounds.supportSizeBound * bounds.pointMultiplicityBound + 1)) ≤
      bounds.toProfile.selected.card := by
  exact bounds.toProfile.card_div_overlapBound_le_selected

/-- The extracted local supports are pairwise vertex-disjoint. -/
theorem extracted_pairwise :
    (bounds.toProfile.selected : Set Item).PairwiseDisjoint
      bounds.packing.support := by
  exact bounds.toProfile.selected_pairwise

end LocalMultiplicityProfile

end StructuralExhaustion.Core.FiniteBoundedOverlap
