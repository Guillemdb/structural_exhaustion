import Mathlib.Tactic
import StructuralExhaustion.Core.FiniteDisjointPacking

namespace StructuralExhaustion.Core.GreedyDisjointPacking

universe uVertex uItem

/-!
# Ordered maximal disjoint packings

This is the reusable, application-independent form of the paper's
"choose a deterministic maximal disjoint family" step.  The input is one
explicit ordered item universe.  The construction scans that list once,
retaining an item precisely when its support is disjoint from the already
retained tail.  It never enumerates families of items or searches for a
maximum-cardinality packing.
-/

/-- Static data for a deterministic greedy packing of finite nonempty
supports.  The explicit item enumeration is the tie-breaking order. -/
structure Profile (Vertex : Type uVertex) (Item : Type uItem) where
  vertices : FinEnum Vertex
  items : FinEnum Item
  support : Item → Finset Vertex
  representative : Item → Vertex
  representative_mem : ∀ item, representative item ∈ support item

namespace Profile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (profile : Profile Vertex Item)

/-- Forget only the scheduling order.  This exposes the generic finite
support mathematics without selecting a maximum family. -/
noncomputable def finiteProfile :
    Core.FiniteDisjointPacking.Profile Vertex Item where
  vertices := profile.vertices
  finiteItems := by
    letI : FinEnum Item := profile.items
    infer_instance
  support := profile.support
  representative := profile.representative
  representative_mem := profile.representative_mem

/-- Test whether one item is support-disjoint from every already selected
item. -/
def compatible (item : Item) (selected : List Item) : Bool := by
  letI : DecidableEq Vertex := profile.vertices.decEq
  exact selected.all fun candidate =>
    decide (Disjoint (profile.support item) (profile.support candidate))

theorem compatible_eq_true_iff (item : Item) (selected : List Item) :
    profile.compatible item selected = true ↔
      ∀ candidate ∈ selected,
        Disjoint (profile.support item) (profile.support candidate) := by
  letI : DecidableEq Vertex := profile.vertices.decEq
  simp [compatible]

/-- Greedy maximal packing in the declared item order.  Recursion is only on
the supplied list; the construction never materializes the powerset of
packings. -/
def greedy : List Item → List Item
  | [] => []
  | item :: tail =>
      let selected := profile.greedy tail
      if profile.compatible item selected then item :: selected else selected

theorem greedy_sublist : ∀ values : List Item,
    (profile.greedy values).Sublist values := by
  intro values
  induction values with
  | nil => simp [greedy]
  | cons item tail ih =>
      simp only [greedy]
      split
      · exact ih.cons_cons item
      · exact ih.trans (List.tail_sublist (item :: tail))

theorem greedy_nodup {values : List Item} (nodup : values.Nodup) :
    (profile.greedy values).Nodup :=
  nodup.sublist (profile.greedy_sublist values)

theorem greedy_pairwise : ∀ values : List Item,
    (profile.greedy values).Pairwise
      (Function.onFun Disjoint profile.support) := by
  intro values
  induction values with
  | nil => simp [greedy]
  | cons item tail ih =>
      simp only [greedy]
      split <;> rename_i decision
      · rw [List.pairwise_cons]
        exact ⟨(profile.compatible_eq_true_iff item _).1 decision, ih⟩
      · exact ih

/-- Every supplied item intersects a selected greedy item. -/
theorem greedy_saturated : ∀ (values : List Item) (item : Item),
    item ∈ values →
      ∃ selected ∈ profile.greedy values,
        ¬Disjoint (profile.support item) (profile.support selected) := by
  classical
  intro values candidate member
  induction values generalizing candidate with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [greedy]
      split <;> rename_i decision
      · rcases member with rfl | tailMember
        · refine ⟨head, by simp, ?_⟩
          exact Finset.not_disjoint_iff.mpr
            ⟨profile.representative head,
              profile.representative_mem head,
              profile.representative_mem head⟩
        · obtain ⟨selected, selectedMem, intersects⟩ :=
            ih candidate tailMember
          exact ⟨selected, by simp [selectedMem], intersects⟩
      · have notAll : ¬∀ selected ∈ profile.greedy tail,
            Disjoint (profile.support head) (profile.support selected) := by
          intro allDisjoint
          exact decision
            ((profile.compatible_eq_true_iff head _).2 allDisjoint)
        push Not at notAll
        rcases member with rfl | tailMember
        · obtain ⟨selected, selectedMem, notDisjoint⟩ := notAll
          exact ⟨selected, selectedMem, notDisjoint⟩
        · exact ih candidate tailMember

/-- The deterministic selected list. -/
noncomputable def values : List Item :=
  profile.greedy profile.items.orderedValues

theorem values_nodup : profile.values.Nodup :=
  profile.greedy_nodup profile.items.nodup_orderedValues

theorem values_pairwise :
    profile.values.Pairwise (Function.onFun Disjoint profile.support) :=
  profile.greedy_pairwise profile.items.orderedValues

/-- Inclusion maximality in the exact form consumed by remainder arguments. -/
theorem values_saturated (item : Item) :
    ∃ selected ∈ profile.values,
      ¬Disjoint (profile.support item) (profile.support selected) :=
  profile.greedy_saturated profile.items.orderedValues item
    (profile.items.mem_orderedValues item)

/-- The selected list, viewed as a generic finite support packing. -/
noncomputable def packing : profile.finiteProfile.Packing := by
  letI : DecidableEq Item := profile.items.decEq
  refine ⟨profile.values.toFinset, ?_⟩
  exact (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
    profile.values_nodup).2 profile.values_pairwise

/-- Pairwise-disjoint nonempty supports inject their representatives into
the host carrier.  This bounds the selected-list audit without any search
over alternative packings. -/
theorem values_length_le_vertices :
    profile.values.length ≤ profile.vertices.card := by
  letI : DecidableEq Item := profile.items.decEq
  calc
    profile.values.length = profile.values.toFinset.card :=
      (List.toFinset_card_of_nodup profile.values_nodup).symm
    _ ≤ profile.vertices.card :=
      profile.finiteProfile.packing_card_le_vertices profile.packing

/-- If an item exists, saturation forces the maximal selected list to be
nonempty. -/
theorem values_nonempty_of_item (item : Item) : profile.values ≠ [] := by
  rcases profile.values_saturated item with ⟨selected, selectedMem, _⟩
  exact List.ne_nil_of_mem selectedMem

end Profile

end StructuralExhaustion.Core.GreedyDisjointPacking
