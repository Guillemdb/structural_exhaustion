import Mathlib

namespace StructuralExhaustion.Core.LocalFiniteCapacity

universe u

/-! Cardinality transfer between two supplied finite lists. -/

theorem nodup_length_le_of_mem
    {α : Type u} [DecidableEq α] {items capacity : List α}
    (nodup : items.Nodup)
    (contained : ∀ item ∈ items, item ∈ capacity) :
    items.length ≤ capacity.length := by
  rw [← List.toFinset_card_of_nodup nodup]
  exact (Finset.card_le_card fun item member => by
    rw [List.mem_toFinset] at member ⊢
    exact contained item member).trans (List.toFinset_card_le capacity)

end StructuralExhaustion.Core.LocalFiniteCapacity
