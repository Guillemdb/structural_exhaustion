import Hypostructure.Core.Finite.Flatten
import Hypostructure.Core.Finite.Partition
import Hypostructure.Core.Finite.SelectedSchedule
import Hypostructure.Core.Residual.Terminal

/-!
# Core capabilities used by cold-branch migration

Neutral fixtures for the reusable Core pieces required by the cold branch:
proof-only terminal continuation, finite predicate partition, and dependent
schedule flattening.  The fixture exposes only abstract schedules and
predicates.
-/

namespace Hypostructure.Fixtures.ColdBranchCoreCapabilities

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

def focus : Focus.Profile Nat :=
  Focus.always Nat

def terminalStage : Terminal.Stage focus :=
  Terminal.execute focus 5

theorem terminal_preserves_predecessor :
    terminalStage.previous = 5 :=
  Terminal.execute_previous focus 5

theorem terminal_work_within :
    focus.selectionBudget.Within 5
      (Terminal.executeCounted focus 5).checks :=
  Terminal.executeCounted_work_within focus 5

def schedule : Enumeration Nat :=
  Enumeration.ofNodupList [0, 1, 2, 3] (by decide)

def selectedScheduleQuery : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active => schedule

def selectedScheduleContract : SelectedSchedule.Contract focus where
  Item := Nat
  selected := selectedScheduleQuery

def selectedScheduleStage : selectedScheduleContract.Stage :=
  selectedScheduleContract.run 5

theorem selectedSchedule_preserves_previous :
    selectedScheduleStage.previous = 5 :=
  selectedScheduleContract.run_previous 5

theorem selectedSchedule_attached_card_exact :
    (selectedScheduleContract.latestAttached.read selectedScheduleStage
        trivial).card =
      schedule.card := by
  have card :=
    selectedScheduleContract.latestAttachedCardExact.read
      selectedScheduleStage trivial
  have schedule_eq :
      (selectedScheduleQuery.read selectedScheduleStage.previous
        trivial).card = schedule.card := by
    simp [selectedScheduleStage, selectedScheduleContract,
      selectedScheduleQuery]
  exact card.trans schedule_eq

theorem selectedSchedule_attached_members :
    ∀ entry ∈
      (selectedScheduleContract.latestAttached.read selectedScheduleStage
        trivial).values,
        entry.1 ∈ schedule.values := by
  intro entry _member
  exact entry.2

def evenPredicate (value : Nat) : Prop :=
  value % 2 = 0

def evenDecidable (value : Nat) : Decidable (evenPredicate value) := by
  unfold evenPredicate
  infer_instance

def partition : Partition.Result schedule evenPredicate :=
  Partition.run schedule evenPredicate evenDecidable

theorem partition_card_exact :
    partition.accepted.card + partition.rejected.card = schedule.card :=
  partition.card_partition

def partitionScheduleQuery : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active => schedule

def focusedPartitionContract :
    Partition.FocusedContract.{1, 0} focus where
  Item := Nat
  schedule := partitionScheduleQuery
  predicate := fun _previous _active value => evenPredicate value
  decidePredicate := fun _previous _active => evenDecidable

def focusedPartitionStage : focusedPartitionContract.Stage :=
  focusedPartitionContract.runStage 5

theorem focusedPartition_preserves_previous :
    focusedPartitionStage.previous = 5 :=
  focusedPartitionContract.runStage_previous 5

theorem focusedPartition_card_exact :
    (focusedPartitionContract.latestAccepted.read focusedPartitionStage trivial).card +
        (focusedPartitionContract.latestRejected.read focusedPartitionStage trivial).card =
      schedule.card := by
  have card :=
    focusedPartitionContract.latestCardPartition.read focusedPartitionStage
      trivial
  have schedule_eq :
      ((focusedPartitionContract.schedule.preserve).read focusedPartitionStage
        trivial).card = schedule.card := by
    simp [focusedPartitionStage, focusedPartitionContract,
      partitionScheduleQuery]
  exact card.trans schedule_eq

def Fibre (_index : Bool) : Type :=
  Bool

def boolFibre (_index : Bool) : Enumeration Bool :=
  Enumeration.ofNodupList [false, true] (by decide)

theorem boolFibre_card (index : Bool) :
    (boolFibre index).card = 2 := by
  cases index <;> rfl

def dependent : DependentEnumeration Bool Fibre where
  indices := Enumeration.ofNodupList [false, true] (by decide)
  fibres := boolFibre

def flattened : Flatten.Result dependent :=
  Flatten.run dependent

theorem flattened_card_sum :
    flattened.flattened.card =
      (dependent.indices.values.map fun i => (dependent.fibres i).card).sum :=
  flattened.card_eq_sum

def dependentScheduleQuery :
    Focus.ActiveQuery focus fun _previous _active =>
      DependentEnumeration Bool Fibre :=
  Focus.ActiveQuery.ofFunction fun _previous _active => dependent

def focusedFlattenContract :
    Flatten.FocusedContract.{1, 0, 0} focus where
  Index := Bool
  Fibre := Fibre
  schedule := dependentScheduleQuery

def focusedFlattenStage : focusedFlattenContract.Stage :=
  focusedFlattenContract.runStage 5

theorem focusedFlatten_preserves_previous :
    focusedFlattenStage.previous = 5 :=
  focusedFlattenContract.runStage_previous 5

theorem focusedFlatten_card_sum :
    (focusedFlattenContract.latestFlattened.read focusedFlattenStage
        trivial).card =
      (dependent.indices.values.map fun i => (dependent.fibres i).card).sum := by
  have card :=
    focusedFlattenContract.latestCardEqSum.read focusedFlattenStage trivial
  have rhs_eq :
      (((focusedFlattenContract.schedule.preserve).read focusedFlattenStage
          trivial).indices.values.map
        fun i =>
          (((focusedFlattenContract.schedule.preserve).read
            focusedFlattenStage trivial).fibres i).card).sum =
        (dependent.indices.values.map fun i => (dependent.fibres i).card).sum := by
    simp [focusedFlattenStage, focusedFlattenContract, dependentScheduleQuery]
  exact card.trans rhs_eq

def focusedFlattenConstantFibres :
    Focus.ActiveQuery focusedFlattenContract.successor fun stage active =>
      ∀ index ∈ ((focusedFlattenContract.schedule.preserve).read stage
          active).indices.values,
        (((focusedFlattenContract.schedule.preserve).read stage
          active).fibres index).card = 2 :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    intro index member
    exact boolFibre_card index

theorem focusedFlatten_card_constant :
    (focusedFlattenContract.latestFlattened.read focusedFlattenStage
        trivial).card =
      2 * dependent.indices.card := by
  have card :=
    (focusedFlattenContract.latestCardEqContributionMul 2
      focusedFlattenConstantFibres).read focusedFlattenStage trivial
  have rhs_eq :
      2 *
          ((focusedFlattenContract.schedule.preserve).read focusedFlattenStage
            trivial).indices.card =
        2 * dependent.indices.card := by
    simp [focusedFlattenStage, focusedFlattenContract, dependentScheduleQuery]
  exact card.trans rhs_eq

#print axioms terminal_work_within
#print axioms selectedSchedule_attached_card_exact
#print axioms selectedSchedule_attached_members
#print axioms partition_card_exact
#print axioms focusedPartition_card_exact
#print axioms flattened_card_sum
#print axioms focusedFlatten_card_sum
#print axioms focusedFlatten_card_constant

end Hypostructure.Fixtures.ColdBranchCoreCapabilities
