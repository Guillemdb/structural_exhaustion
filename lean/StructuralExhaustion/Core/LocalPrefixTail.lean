import Mathlib

namespace StructuralExhaustion.Core.LocalPrefixTail

universe u

/-! A lossless membership split on one supplied finite list. -/

inductive Outcome {α : Type u} (items : List α) (prefixLength : Nat)
    (item : α) : Type u where
  | inPrefix (member : item ∈ items.take prefixLength)
  | inTail (member : item ∈ items.drop prefixLength)

noncomputable def run {α : Type u} (items : List α) (prefixLength : Nat) (item : α)
    (member : item ∈ items) : Outcome items prefixLength item := by
  classical
  by_cases inPrefix : item ∈ items.take prefixLength
  · exact Outcome.inPrefix inPrefix
  · apply Outcome.inTail
    have inSplit : item ∈ items.take prefixLength ++ items.drop prefixLength := by
      rwa [List.take_append_drop]
    exact (List.mem_append.mp inSplit).resolve_left inPrefix

theorem exhaustive {α : Type u} (items : List α) (prefixLength : Nat)
    (item : α) (member : item ∈ items) :
    item ∈ items.take prefixLength ∨ item ∈ items.drop prefixLength := by
  cases run items prefixLength item member with
  | inPrefix member => exact Or.inl member
  | inTail member => exact Or.inr member

theorem prefix_length_le {α : Type u} (items : List α) (prefixLength : Nat) :
    (items.take prefixLength).length ≤ prefixLength := by
  simp

end StructuralExhaustion.Core.LocalPrefixTail
