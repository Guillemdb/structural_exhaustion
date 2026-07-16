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

/-- The extracted supports are pairwise vertex-disjoint. -/
theorem selected_pairwise :
    (profile.selected : Set Item).PairwiseDisjoint profile.packing.support :=
  profile.packing.maximum.2

end Profile

end StructuralExhaustion.Core.FiniteBoundedOverlap
