import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Core.EnumerationCombinators
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.SelectedSurplusMass

open StructuralExhaustion
open scoped BigOperators

universe uItem uAmbient uBranch

/-!
# CT14 accounting on an exact selected local family

This profile scans one already supplied finite item schedule.  Selected items
cost one unit and carry their own positive surplus.  No ambient vertex subset
or family of supports is generated.  The capacity conclusion is therefore the
literal inequality between the selected count and the surplus of the selected
items, followed by the coarser bound by the complete local surplus ledger.
-/

inductive Label
  | selected
  | unselected
  deriving DecidableEq

structure Profile (Item : Type uItem) where
  items : FinEnum Item
  Selected : Item → Prop
  selectedDecidable : ∀ item, Decidable (Selected item)
  surplus : Item → Nat
  positive : ∀ item, 1 ≤ surplus item

namespace Profile

variable {Item : Type uItem} (profile : Profile Item)

def lowerAt (item : Item) : Nat :=
  @ite Nat (profile.Selected item) (profile.selectedDecidable item) 1 0

def capacityAt (item : Item) : Nat :=
  @ite Nat (profile.Selected item) (profile.selectedDecidable item)
    (profile.surplus item) 0

def labelAt (item : Item) : Label :=
  @ite Label (profile.Selected item) (profile.selectedDecidable item)
    .selected .unselected

def capability (problem : Core.Problem.{uAmbient, uBranch}) :
    CT14.Capability problem where
  Member := Item
  members := profile.items
  Label := Label
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ item => profile.lowerAt item
  memberCapacity := fun _ item => some (profile.capacityAt item)
  memberLabel := fun _ item => some (profile.labelAt item)

def input {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.Input (profile.capability problem) context := ⟨⟩

def run {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.ExecutionResult (profile.capability problem) context :=
  CT14.run (profile.capability problem) context (profile.input context)

def selectedCount : Nat := by
  letI : FinEnum Item := profile.items
  exact ∑ item : Item, profile.lowerAt item

@[implicit_reducible] def selectedItems :
    FinEnum {item : Item // profile.Selected item} :=
  Core.Enumeration.subtype profile.items profile.Selected
    profile.selectedDecidable

def selectedSurplus : Nat := by
  letI : FinEnum Item := profile.items
  exact ∑ item : Item, profile.capacityAt item

def totalSurplus : Nat := by
  letI : FinEnum Item := profile.items
  exact ∑ item : Item, profile.surplus item

/-- Lower-mass, capacity-presence, label-presence, and upper-capacity scans,
followed by one comparison.  This counts profile-operator evaluations; an
application whose selection predicate is itself a finite scan must expand
that cost in its thin instantiation. -/
def checks : Nat := 4 * profile.items.card + 1

theorem lowerAt_le_capacityAt (item : Item) :
    profile.lowerAt item ≤ profile.capacityAt item := by
  by_cases selected : profile.Selected item
  · simpa [lowerAt, capacityAt, selected] using profile.positive item
  · simp [lowerAt, capacityAt, selected]

theorem capacityAt_le_surplus (item : Item) :
    profile.capacityAt item ≤ profile.surplus item := by
  by_cases selected : profile.Selected item
  · simp [capacityAt, selected]
  · simp [capacityAt, selected]

theorem selectedCount_le_selectedSurplus :
    profile.selectedCount ≤ profile.selectedSurplus := by
  letI : FinEnum Item := profile.items
  unfold selectedCount selectedSurplus
  exact Finset.sum_le_sum fun item _ => profile.lowerAt_le_capacityAt item

theorem selectedCount_eq_selectedItems_card :
    profile.selectedCount = profile.selectedItems.card := by
  letI : DecidablePred profile.Selected := profile.selectedDecidable
  letI : FinEnum Item := profile.items
  letI : FinEnum {item : Item // profile.Selected item} :=
    profile.selectedItems
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]
  unfold selectedCount lowerAt
  simpa using (Finset.sum_boole (R := Nat) profile.Selected
    (Finset.univ : Finset Item))

theorem selectedSurplus_le_totalSurplus :
    profile.selectedSurplus ≤ profile.totalSurplus := by
  letI : FinEnum Item := profile.items
  unfold selectedSurplus totalSurplus
  exact Finset.sum_le_sum fun item _ => profile.capacityAt_le_surplus item

theorem selectedCount_le_totalSurplus :
    profile.selectedCount ≤ profile.totalSurplus :=
  profile.selectedCount_le_selectedSurplus.trans
    profile.selectedSurplus_le_totalSurplus

theorem lowerMass_eq_selectedCount
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.lowerMass (profile.capability problem) context =
      profile.selectedCount := by
  rfl

theorem upperCapacity_eq_selectedSurplus
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.upperCapacity (profile.capability problem) context =
      profile.selectedSurplus := by
  rfl

theorem run_terminal
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).terminal = .capacity := by
  apply CT14.run_terminal_capacity_of_complete
  · intro item
    exact ⟨profile.capacityAt item, rfl⟩
  · intro item
    exact ⟨profile.labelAt item, rfl⟩
  · rw [profile.lowerMass_eq_selectedCount context,
      profile.upperCapacity_eq_selectedSurplus context]
    exact profile.selectedCount_le_selectedSurplus

theorem run_trace
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] := by
  apply CT14.run_trace_capacity_of_complete
  · intro item
    exact ⟨profile.capacityAt item, rfl⟩
  · intro item
    exact ⟨profile.labelAt item, rfl⟩
  · rw [profile.lowerMass_eq_selectedCount context,
      profile.upperCapacity_eq_selectedSurplus context]
    exact profile.selectedCount_le_selectedSurplus

structure VerifiedStage {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Prop where
  terminal : (profile.run context).terminal = .capacity
  trace : (profile.run context).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  verified : (profile.run context).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace problem (profile.capability problem)
    context (profile.run context).trace
  total : ∃ result : CT14.ExecutionResult (profile.capability problem) context,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace problem
      (profile.capability problem) context result.trace
  localBound : profile.selectedCount ≤ profile.totalSurplus
  workExact : profile.checks = 4 * profile.items.card + 1
  linearWork : profile.checks ≤ 5 * (profile.items.card + 1)

def verifiedStage {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : profile.VerifiedStage context where
  terminal := profile.run_terminal context
  trace := profile.run_trace context
  verified := CT14.run_verified (profile.capability problem) context
    (profile.input context)
  traceValid := CT14.run_trace_valid (profile.capability problem) context
    (profile.input context)
  total := CT14.run_total (profile.capability problem) context
    (profile.input context)
  localBound := profile.selectedCount_le_totalSurplus
  workExact := rfl
  linearWork := by
    unfold checks
    omega

end Profile

end StructuralExhaustion.Graph.SelectedSurplusMass
