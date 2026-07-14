import StructuralExhaustion.Graph.P13FanLabelPacking

namespace StructuralExhaustion.Graph.P13MarkedFanLabelPacking

open StructuralExhaustion

universe uAmbient uBranch uItem

/-!
# CT9 strengthening for a marked non-singleton P13 label

Given the base pairwise-compatible family and one distinguished label
containing two different positions, this profile removes the distinguished
member and runs a second CT9 partition. Two representative slots are assigned
capacity zero because they lie in the closed conflict neighbourhood of those
positions; the remaining six slots have capacity one. Thus at most six other
members remain, and the original family has size at most seven.
-/

structure Profile {Item : Type uItem}
    (base : P13FanLabelPacking.Profile Item) where
  distinguished : Item
  distinguished_mem : distinguished ∈ base.items.values
  first : Fin 13
  second : Fin 13
  first_mem : first ∈ base.attachment distinguished
  second_mem : second ∈ base.attachment distinguished
  positions_distinct : first ≠ second

namespace Profile

variable {Item : Type uItem} {base : P13FanLabelPacking.Profile Item}
    (profile : Profile base)

def otherItems : Core.OrderedCollection Item := by
  letI : DecidableEq Item := base.items.decEq
  exact {
    values := base.items.values.erase profile.distinguished
    nodup := base.items.nodup.erase _
    decEq := base.items.decEq
  }

theorem mem_otherItems_iff (item : Item) :
    item ∈ profile.otherItems.values ↔
      item ≠ profile.distinguished ∧ item ∈ base.items.values := by
  letI : DecidableEq Item := base.items.decEq
  exact base.items.nodup.mem_erase_iff

def firstBlockedSlot : Fin 8 :=
  P13PositionPacking.firstBlockedSlot profile.first

def secondBlockedSlot : Fin 8 :=
  P13PositionPacking.secondBlockedSlot profile.first profile.second

theorem blockedSlots_ne :
    profile.firstBlockedSlot ≠ profile.secondBlockedSlot :=
  P13PositionPacking.blockedSlots_ne profile.first profile.second

noncomputable def capability
    (problem : Core.Problem.{uAmbient, uBranch}) : CT9.Capability problem where
  Item := Item
  Label := Fin 8
  labels := inferInstance
  label := base.slotLabel
  capacity := P13PositionPacking.twoBlockedCapacity
    profile.firstBlockedSlot profile.secondBlockedSlot

noncomputable def input {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT9.Input (profile.capability problem) where
  context := context
  items := profile.otherItems

private theorem not_blocked {item : Item}
    (itemMem : item ∈ profile.otherItems.values) :
    ¬P13PositionPacking.BlockedByPair profile.first profile.second
      (base.representative item) := by
  intro blocked
  have itemNe := (profile.mem_otherItems_iff item).mp itemMem |>.1
  rcases blocked with equal | distance | distance | equal | distance | distance
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.first_mem (Or.inl equal)
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.first_mem
      (Or.inr (Or.inl distance))
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.first_mem
      (Or.inr (Or.inr distance))
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.second_mem (Or.inl equal)
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.second_mem
      (Or.inr (Or.inl distance))
  · exact base.not_positionConflict_of_distinct itemNe
      (base.representative_mem item) profile.second_mem
      (Or.inr (Or.inr distance))

theorem label_ne_firstBlockedSlot {item : Item}
    (itemMem : item ∈ profile.otherItems.values) :
    base.slotLabel item ≠ profile.firstBlockedSlot := by
  intro same
  exact profile.not_blocked itemMem
    (P13PositionPacking.firstSlot_blocked profile.first profile.second
      (base.representative item) same)

theorem label_ne_secondBlockedSlot {item : Item}
    (itemMem : item ∈ profile.otherItems.values) :
    base.slotLabel item ≠ profile.secondBlockedSlot := by
  intro same
  exact profile.not_blocked itemMem
    (P13PositionPacking.secondSlot_blocked profile.first profile.second
      (base.representative item) profile.positions_distinct same)

theorem bounded {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    ∀ label, CT9.fibreCount (profile.capability problem)
      (profile.input context) label ≤
        (profile.capability problem).capacity label := by
  intro label
  change Fin 8 at label
  by_cases blocked : label = profile.firstBlockedSlot ∨
      label = profile.secondBlockedSlot
  · rcases blocked with equal | equal
    · subst label
      have absent : ∀ item ∈ (profile.input context).items.values,
          (profile.capability problem).label item ≠ profile.firstBlockedSlot := by
        intro item itemMem
        simpa [capability] using profile.label_ne_firstBlockedSlot itemMem
      have zero := CT9.fibreCount_eq_zero_of_label_absent
        (profile.capability problem) (profile.input context)
        profile.firstBlockedSlot absent
      change CT9.fibreCount (profile.capability problem)
        (profile.input context) profile.firstBlockedSlot ≤
          P13PositionPacking.twoBlockedCapacity profile.firstBlockedSlot
            profile.secondBlockedSlot profile.firstBlockedSlot
      simpa [P13PositionPacking.twoBlockedCapacity] using zero
    · subst label
      have absent : ∀ item ∈ (profile.input context).items.values,
          (profile.capability problem).label item ≠ profile.secondBlockedSlot := by
        intro item itemMem
        simpa [capability] using profile.label_ne_secondBlockedSlot itemMem
      have zero := CT9.fibreCount_eq_zero_of_label_absent
        (profile.capability problem) (profile.input context)
        profile.secondBlockedSlot absent
      change CT9.fibreCount (profile.capability problem)
        (profile.input context) profile.secondBlockedSlot ≤
          P13PositionPacking.twoBlockedCapacity profile.firstBlockedSlot
            profile.secondBlockedSlot profile.secondBlockedSlot
      simpa [P13PositionPacking.twoBlockedCapacity] using zero
  · have one := CT9.fibreCount_le_one_of_label_injective_on_items
      (profile.capability problem) (profile.input context) (by
        intro left right _leftMem _rightMem same
        exact base.slotLabel_injective (by simpa [capability] using same)) label
    change CT9.fibreCount (profile.capability problem)
      (profile.input context) label ≤
        P13PositionPacking.twoBlockedCapacity profile.firstBlockedSlot
          profile.secondBlockedSlot label
    rw [P13PositionPacking.twoBlockedCapacity, if_neg blocked]
    exact one

noncomputable def run {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT9.BoundedRun (profile.capability problem) (profile.input context) :=
  CT9.runBoundedOfBounded (profile.capability problem) (profile.input context)
    (profile.bounded context)

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
    CT9.totalCapacity (profile.capability problem) = 6 := by
  change (((inferInstance : FinEnum (Fin 8)).orderedValues.map
    (P13PositionPacking.twoBlockedCapacity profile.firstBlockedSlot
      profile.secondBlockedSlot)).sum) = 6
  exact P13PositionPacking.sum_twoBlockedCapacity_eq_six
    profile.firstBlockedSlot profile.secondBlockedSlot profile.blockedSlots_ne

theorem other_cardinality_le_six
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.otherItems.values.length ≤ 6 := by
  have global := CT9.cardinality_le_totalCapacity_of_bounded
    (profile.capability problem) (profile.input context)
    (profile.bounded context)
  rw [profile.totalCapacity problem] at global
  change profile.otherItems.values.length ≤ 6 at global
  exact global

/-- Strong marked-label packing bound from the exact second CT9 run. -/
theorem cardinality_le_seven
    (profile : Profile base)
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    base.items.values.length ≤ 7 := by
  letI : DecidableEq Item := base.items.decEq
  have distinguishedMem : profile.distinguished ∈ base.items.values :=
    profile.2
  have erased := List.length_erase_add_one distinguishedMem
  have others := profile.other_cardinality_le_six context
  change (base.items.values.erase profile.distinguished).length ≤ 6 at others
  omega

end Profile

end StructuralExhaustion.Graph.P13MarkedFanLabelPacking
