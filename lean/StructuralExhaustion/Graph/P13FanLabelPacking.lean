import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Graph.P13PositionPacking

namespace StructuralExhaustion.Graph.P13FanLabelPacking

open StructuralExhaustion

universe uAmbient uBranch uItem

/-!
# CT9 packing of pairwise-compatible P13 attachment labels

The author supplies an exact duplicate-free family, one nonempty attachment
label per family member, and pairwise compatibility at outside-path scale two.
The framework chooses the least representative of every label, maps those
representatives into the fixed eight-slot cover, and runs CT9 with capacity
one.  Compatibility makes the slot map injective, so the exact family has at
most eight members.

Only the eight slots and the supplied member list are scanned.  No attachment
label universe and no family of label subsets is enumerated.
-/

/-- Mathematical input for the representative-packing theorem. -/
structure Profile (Item : Type uItem) where
  LengthOK : Nat → Prop
  items : Core.OrderedCollection Item
  attachment : Item → InducedPathAttachment.Label 13
  nonempty : ∀ item, (attachment item).Nonempty
  compatible : ∀ {left right}, left ≠ right →
    InducedPathAttachment.Compatible 13 LengthOK 2
      (attachment left) (attachment right)
  acceptsFour : LengthOK 4
  acceptsEight : LengthOK 8
  acceptsSixteen : LengthOK 16

namespace Profile

variable {Item : Type uItem} (profile : Profile Item)

/-- Deterministic representative used by the packing proof. -/
noncomputable def representative (item : Item) : Fin 13 :=
  (profile.attachment item).min' (profile.nonempty item)

theorem representative_mem (item : Item) :
    profile.representative item ∈ profile.attachment item :=
  Finset.min'_mem _ _

/-- Closed conflict relation in the thirteen-position certificate graph. -/
def PositionConflict (left right : Fin 13) : Prop :=
  left = right ∨ InducedPathAttachment.positionDistance left right = 4 ∨
    InducedPathAttachment.positionDistance left right = 12

/-- Pairwise scale-two compatibility excludes equal, distance-four, and
distance-twelve cross positions. -/
theorem not_positionConflict_of_distinct {left right : Item}
    (distinct : left ≠ right) {leftPosition rightPosition : Fin 13}
    (leftMem : leftPosition ∈ profile.attachment left)
    (rightMem : rightPosition ∈ profile.attachment right) :
    ¬PositionConflict leftPosition rightPosition := by
  intro conflict
  have forbidden := profile.compatible distinct leftPosition leftMem
    rightPosition rightMem
  rcases conflict with equal | distance | distance
  · subst rightPosition
    exact forbidden (by
      simpa [InducedPathAttachment.crossCycleLength,
        InducedPathAttachment.positionDistance] using profile.acceptsFour)
  · exact forbidden (by
      simpa [InducedPathAttachment.crossCycleLength, distance] using
        profile.acceptsEight)
  · exact forbidden (by
      simpa [InducedPathAttachment.crossCycleLength, distance] using
        profile.acceptsSixteen)

/-- Representative slot, independent of the ambient structural-exhaustion
problem in which CT9 is executed. -/
noncomputable def slotLabel (item : Item) : Fin 8 :=
  P13PositionPacking.slot (profile.representative item)

/-- The eight capacity-one labels used by CT9. -/
noncomputable def capability (problem : Core.Problem.{uAmbient, uBranch}) :
    CT9.Capability problem where
  Item := Item
  Label := Fin 8
  labels := inferInstance
  label := profile.slotLabel
  capacity := fun _slot => 1

/-- Exact active collection; its order is inherited unchanged from the
profile. -/
def input {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT9.Input (profile.capability problem) where
  context := context
  items := profile.items

theorem capacity_one (problem : Core.Problem.{uAmbient, uBranch})
    (slot : (profile.capability problem).Label) :
    (profile.capability problem).capacity slot = 1 :=
  rfl

/-- Compatibility forbids two distinct family members from occupying the
same one of the eight representative slots. -/
theorem slotLabel_injective {left right : Item}
    (same : profile.slotLabel left = profile.slotLabel right) :
    left = right := by
  by_contra distinct
  have compatible := profile.compatible distinct
  have forbidden := compatible
    (profile.representative left) (profile.representative_mem left)
    (profile.representative right) (profile.representative_mem right)
  rcases P13PositionPacking.eq_or_positionDistance_eq_four_of_slot_eq
      (profile.representative left) (profile.representative right) same with
    equal | distance
  · rw [equal] at forbidden
    exact forbidden (by
      simpa [InducedPathAttachment.crossCycleLength,
        InducedPathAttachment.positionDistance] using profile.acceptsFour)
  · exact forbidden (by
      simpa [InducedPathAttachment.crossCycleLength, distance] using
        profile.acceptsEight)

/-- Problem-polymorphic form of representative-slot injectivity. -/
theorem capability_label_injective
    (problem : Core.Problem.{uAmbient, uBranch}) {left right : Item}
    (same : (profile.capability problem).label left =
      (profile.capability problem).label right) :
    left = right := by
  apply profile.slotLabel_injective
  simpa [capability] using same

/-- Pointwise capacity certificate derived from semantic compatibility. -/
theorem bounded {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    ∀ slot, CT9.fibreCount (profile.capability problem)
      (profile.input context) slot ≤ 1 :=
  CT9.fibreCount_le_one_of_label_injective_on_items
    (profile.capability problem) (profile.input context) fun
      _leftMem _rightMem same => profile.capability_label_injective problem same

/-- Exact bounded CT9 execution. -/
def run {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT9.BoundedRun (profile.capability problem) (profile.input context) :=
  CT9.runBoundedOfLabelInjectiveOnItems
    (profile.capability problem) (profile.input context)
    (profile.capacity_one problem) fun
      _leftMem _rightMem same => profile.capability_label_injective problem same

theorem run_terminal {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).execution.terminal = .bounded :=
  (profile.run context).terminal_eq

theorem run_trace {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).execution.trace =
      [.entry, .partition, .overload, .boundedTerminal] :=
  (profile.run context).trace_eq

@[simp] theorem totalCapacity
    (problem : Core.Problem.{uAmbient, uBranch}) :
    CT9.totalCapacity (profile.capability problem) = 8 := by
  change (((inferInstance : FinEnum (Fin 8)).orderedValues.map
    (fun _slot => 1)).sum) = 8
  have sumOnes : ∀ values : List (Fin 8),
      (values.map (fun _slot => 1)).sum = values.length := by
    intro values
    induction values with
    | nil => rfl
    | cons _ tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        omega
  rw [sumOnes, FinEnum.orderedValues_length]
  rfl

/-- Structural fan-label packing bound. -/
theorem cardinality_le_eight {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.items.values.length ≤ 8 := by
  have global := CT9.cardinality_le_totalCapacity_of_label_injective_on_items
    (profile.capability problem) (profile.input context)
    (profile.capacity_one problem) fun
      _leftMem _rightMem same => profile.capability_label_injective problem same
  change profile.items.values.length ≤ 8 at global
  exact global

/-- The complete label scan is linear in the supplied family size with a
fixed factor eight; the exponential universe of all P13 labels is absent. -/
def inspectionBound : Nat := 8 * profile.items.values.length

end Profile

end StructuralExhaustion.Graph.P13FanLabelPacking
