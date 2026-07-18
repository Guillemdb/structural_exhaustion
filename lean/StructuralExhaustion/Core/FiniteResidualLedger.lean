import StructuralExhaustion.Core.FiniteSearch
import Mathlib.Data.Fintype.Sum

namespace StructuralExhaustion.Core.FiniteResidualLedger

universe uOccurrence uEvent uPayload uValue

/-!
# Persistent finite residual ledgers

Occurrences, rather than event values, are the primary finite universe.  Thus
two production steps remain distinct even when they emit equal events.
-/

/-- A finite occurrence-indexed event ledger. -/
structure Ledger (Event : Type uEvent) where
  Occurrence : Type uOccurrence
  occurrences : FinEnum Occurrence
  event : Occurrence → Event

namespace Ledger

variable {Event : Type uEvent}

/-- The exact deterministic occurrence order. -/
noncomputable def entries (ledger : Ledger.{uOccurrence, uEvent} Event) :
    List ledger.Occurrence :=
  ledger.occurrences.orderedValues

/-- One check per literal occurrence. -/
noncomputable def checks (ledger : Ledger.{uOccurrence, uEvent} Event) : Nat :=
  ledger.entries.length

@[simp] theorem checks_exact
    (ledger : Ledger.{uOccurrence, uEvent} Event) :
    ledger.checks = ledger.occurrences.card := by
  simp [checks, entries]

theorem occurrence_mem
    (ledger : Ledger.{uOccurrence, uEvent} Event)
    (occurrence : ledger.Occurrence) : occurrence ∈ ledger.entries :=
  ledger.occurrences.mem_orderedValues occurrence

/-- Empty persistent ledger. -/
noncomputable def empty : Ledger.{0, uEvent} Event where
  Occurrence := PEmpty
  occurrences := inferInstance
  event := PEmpty.elim

@[simp] theorem empty_checks : (empty : Ledger Event).checks = 0 := by
  rw [checks_exact]
  rfl

/-- One exact emitted occurrence. -/
noncomputable def singleton (event : Event) : Ledger.{0, uEvent} Event where
  Occurrence := PUnit
  occurrences := inferInstance
  event := fun _ => event

@[simp] theorem singleton_event (event : Event)
    (occurrence : (singleton event).Occurrence) :
    (singleton event).event occurrence = event :=
  rfl

@[simp] theorem singleton_checks (event : Event) :
    (singleton event).checks = 1 := by
  rw [checks_exact]
  rfl

/-- Persistent append.  The sum tag is the occurrence identity; equal events
on the two sides are never identified. -/
noncomputable def append
    (left right : Ledger.{uOccurrence, uEvent} Event) :
    Ledger.{uOccurrence, uEvent} Event where
  Occurrence := Sum left.Occurrence right.Occurrence
  occurrences := by
    letI : FinEnum left.Occurrence := left.occurrences
    letI : FinEnum right.Occurrence := right.occurrences
    infer_instance
  event
    | .inl occurrence => left.event occurrence
    | .inr occurrence => right.event occurrence

@[simp] theorem append_event_left
    (left right : Ledger.{uOccurrence, uEvent} Event)
    (occurrence : left.Occurrence) :
    (left.append right).event (.inl occurrence) = left.event occurrence :=
  rfl

@[simp] theorem append_event_right
    (left right : Ledger.{uOccurrence, uEvent} Event)
    (occurrence : right.Occurrence) :
    (left.append right).event (.inr occurrence) = right.event occurrence :=
  rfl

@[simp] theorem append_checks
    (left right : Ledger.{uOccurrence, uEvent} Event) :
    (left.append right).checks = left.checks + right.checks := by
  letI : FinEnum left.Occurrence := left.occurrences
  letI : FinEnum right.Occurrence := right.occurrences
  have sumCard : FinEnum.card (Sum left.Occurrence right.Occurrence) =
      FinEnum.card left.Occurrence + FinEnum.card right.Occurrence := by
    rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard,
      FinEnum.card_eq_fintypeCard, Fintype.card_sum]
  rw [checks_exact, checks_exact, checks_exact]
  calc
    (left.append right).occurrences.card =
        (inferInstance : FinEnum
          (Sum left.Occurrence right.Occurrence)).card :=
      FinEnum.card_unique _ _
    _ = (inferInstance : FinEnum left.Occurrence).card +
        (inferInstance : FinEnum right.Occurrence).card := sumCard
    _ = left.occurrences.card + right.occurrences.card :=
      congrArg₂ Nat.add (FinEnum.card_unique _ _) (FinEnum.card_unique _ _)

/-- Change only the event view; occurrence identity and order are unchanged. -/
noncomputable def map {Other : Type uValue}
    (ledger : Ledger.{uOccurrence, uEvent} Event) (f : Event → Other) :
    Ledger.{uOccurrence, uValue} Other where
  Occurrence := ledger.Occurrence
  occurrences := ledger.occurrences
  event := f ∘ ledger.event

@[simp] theorem map_event {Other : Type uValue}
    (ledger : Ledger.{uOccurrence, uEvent} Event) (f : Event → Other)
    (occurrence : ledger.Occurrence) :
    (ledger.map f).event occurrence = f (ledger.event occurrence) :=
  rfl

/-- Keep an explicitly decidable subfamily of existing occurrences. -/
noncomputable def restrict
    (ledger : Ledger.{uOccurrence, uEvent} Event)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    Ledger.{uOccurrence, uEvent} Event where
  Occurrence := {occurrence : ledger.Occurrence // keep occurrence}
  occurrences := by
    letI : FinEnum ledger.Occurrence := ledger.occurrences
    letI : DecidablePred keep := keepDecidable
    infer_instance
  event := fun occurrence => ledger.event occurrence.1

@[simp] theorem restrict_event
    (ledger : Ledger.{uOccurrence, uEvent} Event)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence))
    (occurrence : (ledger.restrict keep keepDecidable).Occurrence) :
    (ledger.restrict keep keepDecidable).event occurrence =
      ledger.event occurrence.1 :=
  rfl

/-- An exact occurrence embedding between ledgers with the same event type. -/
structure Embedding
    (source target : Ledger.{uOccurrence, uEvent} Event) where
  occurrence : source.Occurrence → target.Occurrence
  injective : Function.Injective occurrence
  event_exact : ∀ item, target.event (occurrence item) = source.event item

noncomputable def leftEmbedding
    (left right : Ledger.{uOccurrence, uEvent} Event) :
    Embedding left (left.append right) where
  occurrence := Sum.inl
  injective := Sum.inl_injective
  event_exact := fun _ => rfl

noncomputable def rightEmbedding
    (left right : Ledger.{uOccurrence, uEvent} Event) :
    Embedding right (left.append right) where
  occurrence := Sum.inr
  injective := Sum.inr_injective
  event_exact := fun _ => rfl

/-- Dependent data attached to every exact occurrence. -/
structure View (ledger : Ledger.{uOccurrence, uEvent} Event) where
  Payload : ledger.Occurrence → Type uPayload
  value : ∀ occurrence, Payload occurrence

namespace View

variable {ledger : Ledger.{uOccurrence, uEvent} Event}

/-- Dependent projection retaining the occurrence together with its
occurrence-indexed value. -/
def projection (view : View.{uOccurrence, uEvent, uPayload} ledger)
    (occurrence : ledger.Occurrence) :
    Σ item, view.Payload item :=
  ⟨occurrence, view.value occurrence⟩

/-- Restrict a dependent view along the exact subtype occurrence embedding. -/
noncomputable def restrict
    (view : View.{uOccurrence, uEvent, uPayload} ledger)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    View.{uOccurrence, uEvent, uPayload}
      (ledger.restrict keep keepDecidable) where
  Payload := fun occurrence => view.Payload occurrence.1
  value := fun occurrence => view.value occurrence.1

@[simp] theorem restrict_value
    (view : View.{uOccurrence, uEvent, uPayload} ledger)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence))
    (occurrence : (ledger.restrict keep keepDecidable).Occurrence) :
    (view.restrict keep keepDecidable).value occurrence =
      view.value occurrence.1 :=
  rfl

/-- Append dependent views along the tagged append occurrence identity. -/
noncomputable def append
    {left right : Ledger.{uOccurrence, uEvent} Event}
    (leftView : View.{uOccurrence, uEvent, uPayload} left)
    (rightView : View.{uOccurrence, uEvent, uPayload} right) :
    View.{uOccurrence, uEvent, uPayload} (left.append right) where
  Payload
    | .inl occurrence => leftView.Payload occurrence
    | .inr occurrence => rightView.Payload occurrence
  value
    | .inl occurrence => leftView.value occurrence
    | .inr occurrence => rightView.value occurrence

@[simp] theorem append_value_left
    {left right : Ledger.{uOccurrence, uEvent} Event}
    (leftView : View.{uOccurrence, uEvent, uPayload} left)
    (rightView : View.{uOccurrence, uEvent, uPayload} right)
    (occurrence : left.Occurrence) :
    (leftView.append rightView).value (.inl occurrence) =
      leftView.value occurrence :=
  rfl

@[simp] theorem append_value_right
    {left right : Ledger.{uOccurrence, uEvent} Event}
    (leftView : View.{uOccurrence, uEvent, uPayload} left)
    (rightView : View.{uOccurrence, uEvent, uPayload} right)
    (occurrence : right.Occurrence) :
    (leftView.append rightView).value (.inr occurrence) =
      rightView.value occurrence :=
  rfl

end View

end Ledger

end StructuralExhaustion.Core.FiniteResidualLedger
