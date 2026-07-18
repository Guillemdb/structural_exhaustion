import StructuralExhaustion.Core.FiniteProducedSupportLedger

namespace StructuralExhaustion.Examples.FiniteProducedSupportLedger

open StructuralExhaustion

inductive Event
  | typeB
  | route8
  deriving DecidableEq

def support : Event → Finset (Fin 6)
  | .typeB => {0, 1}
  | .route8 => {4, 5}

def initial : Core.FiniteProducedSupportLedger.Ledger Event (Fin 6) :=
  .empty inferInstance support

def accumulated := (initial.record .typeB).record .route8

theorem exact_event_order : accumulated.entries = [.typeB, .route8] := rfl

theorem recognizes_first_produced_support :
    Event.route8 ∈ accumulated.entries ∧
      accumulated.Meets 4 .route8 := by
  simp [accumulated, initial,
    Core.FiniteProducedSupportLedger.Ledger.Meets,
    Core.FiniteProducedSupportLedger.Ledger.record,
    Core.FiniteProducedSupportLedger.Ledger.empty, support]

theorem append_cost_exact : accumulated.checks = 2 := rfl

inductive OtherEvent
  | compression
  deriving DecidableEq

def otherSupport : OtherEvent → Finset (Fin 6)
  | .compression => {2, 3}

def other : Core.FiniteProducedSupportLedger.Ledger OtherEvent (Fin 6) :=
  (Core.FiniteProducedSupportLedger.Ledger.empty inferInstance
    otherSupport).record .compression

def combined := accumulated.sum other

theorem combined_keeps_exact_event_order :
    combined.entries =
      [.inl .typeB, .inl .route8, .inr .compression] := by
  native_decide

theorem combined_preserves_right_support :
    Sum.inr OtherEvent.compression ∈ combined.entries ∧
      combined.Meets 2 (Sum.inr OtherEvent.compression) := by
  simp [combined, accumulated, initial, other,
    Core.FiniteProducedSupportLedger.Ledger.Meets,
    Core.FiniteProducedSupportLedger.Ledger.sum,
    Core.FiniteProducedSupportLedger.Ledger.record,
    Core.FiniteProducedSupportLedger.Ledger.empty, otherSupport]

theorem combined_cost_exact : combined.checks = 3 := by
  simp [combined, accumulated, initial, other,
    Core.FiniteProducedSupportLedger.Ledger.sum,
    Core.FiniteProducedSupportLedger.Ledger.record,
    Core.FiniteProducedSupportLedger.Ledger.empty,
    Core.FiniteProducedSupportLedger.Ledger.checks]

/-! Two equal emitted entries remain two distinct producer occurrences. -/

noncomputable def firstTypeBSchedule :=
  Core.FiniteProducedSupportLedger.OccurrenceSchedule.singleton Event.typeB

noncomputable def secondTypeBSchedule :=
  Core.FiniteProducedSupportLedger.OccurrenceSchedule.singleton Event.typeB

noncomputable def repeatedTypeBSchedule :=
  firstTypeBSchedule.append secondTypeBSchedule

theorem repeated_left_occurrence_is_recorded
    (occurrence : firstTypeBSchedule.Occurrence) :
    repeatedTypeBSchedule.event (.inl occurrence) = Event.typeB :=
  rfl

theorem repeated_right_occurrence_is_recorded
    (occurrence : secondTypeBSchedule.Occurrence) :
    repeatedTypeBSchedule.event (.inr occurrence) = Event.typeB :=
  rfl

theorem repeated_occurrences_are_distinct
    (left : firstTypeBSchedule.Occurrence)
    (right : secondTypeBSchedule.Occurrence) :
    (Sum.inl left : repeatedTypeBSchedule.Occurrence) ≠ Sum.inr right := by
  simp

theorem repeated_left_occurrence_mem
    (occurrence : firstTypeBSchedule.Occurrence) :
    repeatedTypeBSchedule.event (.inl occurrence) ∈
      (repeatedTypeBSchedule.ledger (Vertex := Fin 6) inferInstance support).entries :=
  repeatedTypeBSchedule.occurrence_mem inferInstance support (.inl occurrence)

end StructuralExhaustion.Examples.FiniteProducedSupportLedger
