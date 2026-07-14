import Mathlib.Tactic
import StructuralExhaustion.Graph.InducedPathAttachment

namespace StructuralExhaustion.Graph.P13PositionPacking

/-!
# Cached eight-slot packing for a thirteen-position path

This module contains the only constant-size arithmetic behind the fan-label
packing profile.  It partitions the thirteen path positions into eight pairs
or singletons, with positions in a common slot either equal or four apart.
The proof is compiled once in this small dependency and never enumerates
attachment labels or label families.
-/

/-- Eight fixed slots covering the positions `0, ..., 12`.  Every nontrivial
slot consists of two positions at distance four. -/
def slot (position : Fin 13) : Fin 8 :=
  match position.1 with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 1
  | 9 => 3
  | 10 => 5
  | 11 => 7
  | 12 => 1
  | _ => 0

/-- The exact certificate checked by the fixed slot table.  This is a
thirteen-by-thirteen arithmetic case split (169 tiny goals), isolated here so
its compiled result is reused by all downstream graph profiles. -/
theorem eq_or_positionDistance_eq_four_of_slot_eq
    (left right : Fin 13) (same : slot left = slot right) :
    left = right ∨
      InducedPathAttachment.positionDistance left right = 4 := by
  fin_cases left <;> fin_cases right <;>
    simp [slot, InducedPathAttachment.positionDistance] at same ⊢

/-- The partner slot in one of the four two-slot components. -/
def companion (label : Fin 8) : Fin 8 :=
  match label.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | _ => 0

theorem companion_ne (label : Fin 8) : companion label ≠ label := by
  fin_cases label <;> decide

/-- First slot blocked by a selected attachment position. -/
def firstBlockedSlot (first : Fin 13) : Fin 8 := slot first

/-- A second blocked slot. If the selected positions occupy different slots,
use the second position's slot. If they occupy one matched slot, their closed
neighbourhoods cover its companion slot. -/
def secondBlockedSlot (first second : Fin 13) : Fin 8 :=
  if slot first = slot second then companion (slot first) else slot second

theorem blockedSlots_ne (first second : Fin 13) :
    firstBlockedSlot first ≠ secondBlockedSlot first second := by
  unfold firstBlockedSlot secondBlockedSlot
  split
  · exact (companion_ne (slot first)).symm
  · simpa [eq_comm]

/-- A position is removed by the closed conflict neighbourhood of either of
two selected positions. -/
def BlockedByPair (first second position : Fin 13) : Prop :=
  position = first ∨
    InducedPathAttachment.positionDistance position first = 4 ∨
    InducedPathAttachment.positionDistance position first = 12 ∨
    position = second ∨
    InducedPathAttachment.positionDistance position second = 4 ∨
    InducedPathAttachment.positionDistance position second = 12

instance (first second position : Fin 13) :
    Decidable (BlockedByPair first second position) := by
  unfold BlockedByPair
  infer_instance

theorem firstSlot_blocked (first second position : Fin 13)
    (same : slot position = firstBlockedSlot first) :
    BlockedByPair first second position := by
  rcases eq_or_positionDistance_eq_four_of_slot_eq position first same with
    equal | distance
  · exact Or.inl equal
  · exact Or.inr (Or.inl distance)


/-- Closed constant-size certificate for the second blocked slot. It checks
`13³ = 2197` triples by kernel evaluation in this isolated module; downstream
compilation reuses the resulting object file. -/
private theorem secondSlotBlockedTable :
    ∀ first second position : Fin 13, first ≠ second →
      slot position = secondBlockedSlot first second →
        BlockedByPair first second position := by
  decide

/-- The second selected slot is also completely covered. The only finite
arithmetic is the fixed thirteen-position table, cached in this module. -/
theorem secondSlot_blocked (first second position : Fin 13)
    (distinct : first ≠ second)
    (same : slot position = secondBlockedSlot first second) :
    BlockedByPair first second position :=
  secondSlotBlockedTable first second position distinct same

/-- Capacity zero on two blocked slots and one elsewhere. -/
def twoBlockedCapacity (first second : Fin 8) (label : Fin 8) : Nat :=
  if label = first ∨ label = second then 0 else 1

/-- Exact total capacity of the eight-slot universe after blocking two
distinct slots. This is a cached 8×8 constant check. -/
theorem sum_twoBlockedCapacity_eq_six (first second : Fin 8)
    (distinct : first ≠ second) :
    (((inferInstance : FinEnum (Fin 8)).orderedValues.map
      (twoBlockedCapacity first second)).sum) = 6 := by
  have table : ∀ first second : Fin 8, first ≠ second →
      (((inferInstance : FinEnum (Fin 8)).orderedValues.map
        (twoBlockedCapacity first second)).sum) = 6 := by
    decide
  exact table first second distinct

end StructuralExhaustion.Graph.P13PositionPacking
