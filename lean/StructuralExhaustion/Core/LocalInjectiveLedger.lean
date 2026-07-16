import Mathlib

namespace StructuralExhaustion.Core.LocalInjectiveLedger

universe uIndex uEntry uLabel

/-!
# Aggregate injective ledger from explicit local schedules

The profile below aggregates only the entries supplied for an explicit list
of local indices.  Local labels must be injective on each schedule and labels
from distinct indices must be disjoint.  These two proof obligations give a
duplicate-free global label ledger and the corresponding local lower-bound
sum.  No ambient universe is constructed or searched.
-/

structure Profile (Index : Type uIndex) (Entry : Type uEntry)
    (Label : Type uLabel) where
  indices : List Index
  entries : Index → List Entry
  entriesNodup : ∀ index, (entries index).Nodup
  label : Index → Entry → Label
  localInjective : ∀ index {left right},
    left ∈ entries index → right ∈ entries index →
      label index left = label index right → left = right
  separated : ∀ {leftIndex rightIndex},
    leftIndex ≠ rightIndex →
      ∀ {left right}, left ∈ entries leftIndex →
        right ∈ entries rightIndex →
          label leftIndex left ≠ label rightIndex right

namespace Profile

variable {Index : Type uIndex} {Entry : Type uEntry} {Label : Type uLabel}
variable (profile : Profile Index Entry Label)

def localLabels (index : Index) : List Label :=
  (profile.entries index).map (profile.label index)

def labels : List Label :=
  profile.indices.flatMap profile.localLabels

theorem localLabels_nodup (index : Index) :
    (profile.localLabels index).Nodup := by
  apply List.Nodup.map_on
  intro left leftMem right rightMem equal
  exact profile.localInjective index leftMem rightMem equal
  exact profile.entriesNodup index

private theorem localLabels_disjoint {leftIndex rightIndex : Index}
    (distinct : leftIndex ≠ rightIndex) :
    List.Disjoint (profile.localLabels leftIndex)
      (profile.localLabels rightIndex) := by
  rw [List.disjoint_left]
  intro label leftMem rightMem
  rw [localLabels, List.mem_map] at leftMem rightMem
  rcases leftMem with ⟨left, leftMember, rfl⟩
  rcases rightMem with ⟨right, rightMember, equal⟩
  exact profile.separated distinct leftMember rightMember equal.symm

theorem labels_nodup (indicesNodup : profile.indices.Nodup) :
    profile.labels.Nodup := by
  rw [labels, List.nodup_flatMap]
  constructor
  · intro index _member
    exact profile.localLabels_nodup index
  · exact (List.nodup_iff_pairwise_ne.mp indicesNodup).imp fun distinct =>
      profile.localLabels_disjoint distinct

theorem labels_length :
    profile.labels.length =
      (profile.indices.map fun index => (profile.entries index).length).sum := by
  rw [labels, List.length_flatMap]
  simp [localLabels]

/-- Summing a proved local lower bound over the explicit index list. -/
theorem threshold_mul_indices_le_labels_length (threshold : Nat)
    (large : ∀ index ∈ profile.indices,
      threshold ≤ (profile.entries index).length) :
    threshold * profile.indices.length ≤ profile.labels.length := by
  rw [profile.labels_length]
  have sumBound : ∀ indices : List Index,
      (∀ index ∈ indices,
        threshold ≤ (profile.entries index).length) →
      threshold * indices.length ≤
        (indices.map fun index => (profile.entries index).length).sum := by
    intro indices allLarge
    induction indices with
    | nil => simp
    | cons index rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have head := allLarge index (by simp)
        have tail : ∀ other ∈ rest,
            threshold ≤ (profile.entries other).length := by
          intro other member
          exact allLarge other (by simp [member])
        have restBound := ih tail
        rw [Nat.mul_add, Nat.mul_one,
          Nat.add_comm (threshold * rest.length) threshold]
        exact Nat.add_le_add head restBound
  exact sumBound profile.indices large

/-- One label computation for each actual stored local entry. -/
def visibleChecks : Nat := profile.labels.length

end Profile

end StructuralExhaustion.Core.LocalInjectiveLedger
