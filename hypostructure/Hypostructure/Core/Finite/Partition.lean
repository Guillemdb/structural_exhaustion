import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Focus

/-!
# Exact finite predicate partitions

The framework owns the retained/discarded split of one residual-owned finite
schedule.  Callers provide only a decidable predicate on scheduled entries.
The output keeps both subfamilies as typed exact schedules and proves the
lossless cardinality identity.
-/

namespace Hypostructure.Core.Finite.Partition

open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

universe uPrevious u

variable {α : Type u}

private def acceptedCandidate (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (value : α) : Option {value // predicate value} :=
  if proof : predicate value then some ⟨value, proof⟩ else none

private def rejectedCandidate (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (value : α) : Option {value // Not (predicate value)} :=
  if proof : predicate value then none else some ⟨value, proof⟩

/-- A lossless split of one exact schedule into entries satisfying and
failing a decidable predicate. -/
structure Result (schedule : Enumeration α) (predicate : α -> Prop) where
  accepted : Enumeration {value // predicate value}
  rejected : Enumeration {value // Not (predicate value)}
  card_partition : accepted.card + rejected.card = schedule.card

namespace Result

/-- Number of accepted entries. -/
def acceptedCard {schedule : Enumeration α} {predicate : α -> Prop}
    (result : Result schedule predicate) : Nat :=
  result.accepted.card

/-- Number of rejected entries. -/
def rejectedCard {schedule : Enumeration α} {predicate : α -> Prop}
    (result : Result schedule predicate) : Nat :=
  result.rejected.card

theorem accepted_add_rejected {schedule : Enumeration α}
    {predicate : α -> Prop} (result : Result schedule predicate) :
    result.acceptedCard + result.rejectedCard = schedule.card :=
  result.card_partition

end Result

private theorem filterMap_partition_length (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (values : List α) :
    (values.filterMap (acceptedCandidate predicate decidePredicate)).length +
      (values.filterMap (rejectedCandidate predicate decidePredicate)).length =
        values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.filterMap_cons]
      by_cases h : predicate head
      · simp [acceptedCandidate, rejectedCandidate, h]
        have ih' := ih
        simp [acceptedCandidate, rejectedCandidate] at ih'
        omega
      · simp [acceptedCandidate, rejectedCandidate, h]
        have ih' := ih
        simp [acceptedCandidate, rejectedCandidate] at ih'
        omega

/-- Execute the exact partition in schedule order. -/
def run (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    Result schedule predicate where
  accepted :=
    { values := schedule.values.filterMap
        (acceptedCandidate predicate decidePredicate)
      nodup := schedule.nodup.filterMap (by
        intro left right value leftMem rightMem
        simp only [acceptedCandidate] at leftMem rightMem
        by_cases leftH : predicate left <;>
          by_cases rightH : predicate right <;>
          simp [leftH, rightH] at leftMem rightMem
        have left_eq : left = value.1 := congrArg Subtype.val leftMem
        have right_eq : right = value.1 := congrArg Subtype.val rightMem
        exact left_eq.trans right_eq.symm)
      decEq := by
        letI : DecidableEq α := schedule.decEq
        exact inferInstance }
  rejected :=
    { values := schedule.values.filterMap
        (rejectedCandidate predicate decidePredicate)
      nodup := schedule.nodup.filterMap (by
        intro left right value leftMem rightMem
        simp only [rejectedCandidate] at leftMem rightMem
        by_cases leftH : predicate left <;>
          by_cases rightH : predicate right <;>
          simp [leftH, rightH] at leftMem rightMem
        have left_eq : left = value.1 := congrArg Subtype.val leftMem
        have right_eq : right = value.1 := congrArg Subtype.val rightMem
        exact left_eq.trans right_eq.symm)
      decEq := by
        letI : DecidableEq α := schedule.decEq
        exact inferInstance }
  card_partition := by
    simpa [Enumeration.card] using
      filterMap_partition_length predicate decidePredicate schedule.values

@[simp] theorem accepted_values {schedule : Enumeration α}
    {predicate : α -> Prop}
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (run schedule predicate decidePredicate).accepted.values =
      schedule.values.filterMap
        (acceptedCandidate predicate decidePredicate) :=
  rfl

@[simp] theorem rejected_values {schedule : Enumeration α}
    {predicate : α -> Prop}
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (run schedule predicate decidePredicate).rejected.values =
      schedule.values.filterMap
        (rejectedCandidate predicate decidePredicate) :=
  rfl

/-- Resource-payment adapter for discarded entries.  The payment proof is a
contract fact about the predicate and resource; Core registers it against the
rejected exact schedule so applications do not create a separate loss object. -/
structure PaidDiscard (schedule : Enumeration α) (predicate : α -> Prop)
    (resource : Nat) where
  partition : Result schedule predicate
  rejected_le_resource : partition.rejected.card <= resource

/-- Build a paid-discard certificate from a problem-provided resource law. -/
def paidDiscard (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (resource : Nat)
    (payment : (run schedule predicate decidePredicate).rejected.card <=
      resource) :
    PaidDiscard schedule predicate resource where
  partition := run schedule predicate decidePredicate
  rejected_le_resource := payment

/-! ## Focused residual executor -/

/-- Residual-owned finite partition contract.  Consumers provide only the
active schedule, predicate, and predicate decider.  Core runs the lossless
partition and stores the exact accepted/rejected schedules in the ledger. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  schedule : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Item
  predicate : (previous : Previous) -> focus.Active previous -> Item -> Prop
  decidePredicate : (previous : Previous) -> (active : focus.Active previous) ->
    (item : Item) -> Decidable (predicate previous active item)

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Pure finite partition seen at one active predecessor. -/
def partitionAt (previous : Previous) (active : focus.Active previous) :
    Result (contract.schedule.read previous active)
      (contract.predicate previous active) :=
  run (contract.schedule.read previous active)
    (contract.predicate previous active)
    (contract.decidePredicate previous active)

/-- Focused stage carrying exactly one Core-owned partition result. -/
abbrev Stage :=
  Focus.Stage focus fun previous active =>
    Result (contract.schedule.read previous active)
      (contract.predicate previous active)

/-- Execute the partition and register the accepted/rejected schedules. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    contract.partitionAt previous active

/-- Uncounted public executor. -/
def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

/-- Public CT-style executor spelling. -/
abbrev runStage (previous : Previous) : contract.Stage :=
  contract.execute previous

@[simp] theorem execute_previous (previous : Previous) :
    (contract.execute previous).previous = previous :=
  Focus.runCounted_previous focus previous _

@[simp] theorem runStage_previous (previous : Previous) :
    (contract.runStage previous).previous = previous :=
  contract.execute_previous previous

theorem executeCounted_checks (previous : Previous) :
    (contract.executeCounted previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    Result (contract.schedule.read previous active)
      (contract.predicate previous active)

/-- Read the complete partition result from the newest ledger extension. -/
def latestResult :
    Focus.ActiveQuery contract.successor fun stage active =>
      Result (contract.schedule.read stage.previous active)
        (contract.predicate stage.previous active) :=
  Focus.ActiveQuery.latest

/-- Read the accepted exact schedule from the newest ledger extension. -/
def latestAccepted :
    Focus.ActiveQuery contract.successor fun stage active =>
      Enumeration {value // contract.predicate stage.previous active value} :=
  contract.latestResult.map fun _stage _active result =>
    result.accepted

/-- Read the rejected exact schedule from the newest ledger extension. -/
def latestRejected :
    Focus.ActiveQuery contract.successor fun stage active =>
      Enumeration {value // Not (contract.predicate stage.previous active value)} :=
  contract.latestResult.map fun _stage _active result =>
    result.rejected

/-- Read the lossless cardinality identity from the newest ledger extension. -/
def latestCardPartition :
    Focus.ActiveQuery contract.successor fun stage active =>
      (contract.latestAccepted.read stage active).card +
          (contract.latestRejected.read stage active).card =
        ((contract.schedule.preserve).read stage active).card :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (contract.latestResult.read stage active).card_partition

end FocusedContract

end Hypostructure.Core.Finite.Partition

/-! ## Generic ordered label partitions -/

namespace Hypostructure.Core.Finite.OrderedPartition

open Hypostructure.Core.Finite

universe u v

variable {Carrier : Type u} {Label : Type v}

/-! An ordered label partition scans an exact finite carrier schedule once and
keeps the first occurrence of each label.  The carrier semantics remain the
domain contract; the order, duplicate removal, coverage, and work bound are
Core-owned. -/

noncomputable def labels (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) : List Label := by
  classical
  exact (schedule.values.map labelOf).dedup

theorem labels_nodup (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) :
    (labels schedule labelOf).Nodup := by
  classical
  exact List.nodup_dedup _

theorem labels_complete (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) (label : Label) :
    label ∈ labels schedule labelOf ↔
      ∃ carrier ∈ schedule.values, labelOf carrier = label := by
  classical
  simp [labels]

theorem labels_length_le (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) :
    (labels schedule labelOf).length ≤ schedule.card := by
  classical
  calc
    (labels schedule labelOf).length ≤
        (schedule.values.map labelOf).length := by
      exact (List.dedup_sublist _).length_le
    _ = schedule.card := by simp [Enumeration.card]

noncomputable def members (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) (label : Label) : Finset Carrier := by
  classical
  exact schedule.toFinset.filter fun carrier => labelOf carrier = label

@[simp] theorem mem_members_iff (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) (label : Label) (carrier : Carrier) :
    carrier ∈ members schedule labelOf label ↔
      carrier ∈ schedule.values ∧ labelOf carrier = label := by
  classical
  simp [members]

theorem members_disjoint (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) {left right : Label}
    (different : left ≠ right) :
    Disjoint (members schedule labelOf left)
      (members schedule labelOf right) := by
  classical
  apply Finset.disjoint_left.mpr
  intro carrier leftMem rightMem
  have leftEq := (mem_members_iff schedule labelOf left carrier).mp leftMem
  have rightEq := (mem_members_iff schedule labelOf right carrier).mp rightMem
  exact different (leftEq.2.symm.trans rightEq.2)

theorem members_cover (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) {carrier : Carrier}
    (carrierMem : carrier ∈ schedule.values) :
    carrier ∈ members schedule labelOf (labelOf carrier) := by
  exact (mem_members_iff schedule labelOf _ _).mpr ⟨carrierMem, rfl⟩

def checks (schedule : Enumeration Carrier) : Nat := schedule.card

theorem checks_linear (schedule : Enumeration Carrier) :
    checks schedule ≤ schedule.card := le_rfl

end Hypostructure.Core.Finite.OrderedPartition
