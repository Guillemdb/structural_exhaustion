import StructuralExhaustion.Core.FiniteResidualLedger

namespace StructuralExhaustion.Core.CertifiedResidualLedger

universe uOccurrence uInput uEvent uOther uSeed

/-!
# Certified persistent residual ledgers

Problem code proves one local producer theorem.  The framework lifts that
theorem over the exact finite schedule of actual producer occurrences, keeps
duplicate event values distinct, and composes later certified attachments.
-/

/-- One problem-specific theorem output ready to be recorded. -/
structure Emission (Event : Type uEvent) (Valid : Event → Prop) where
  event : Event
  certified : Valid event

/-- A persistent occurrence ledger together with the theorem established for
every literal producer occurrence. -/
structure Ledger (Event : Type uEvent) (Valid : Event → Prop) where
  residuals : FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event
  certified : ∀ occurrence, Valid (residuals.event occurrence)

namespace Ledger

variable {Event : Type uEvent} {Valid : Event → Prop}

/-- Empty certified proof state. -/
noncomputable def empty : Ledger.{0, uEvent} Event Valid where
  residuals := .empty
  certified := fun occurrence => nomatch occurrence

/-- A single theorem output, retaining one exact producer occurrence. -/
noncomputable def singleton (emission : Emission Event Valid) :
    Ledger.{0, uEvent} Event Valid where
  residuals := .singleton emission.event
  certified := fun _ => emission.certified

/-- `ledger.add event theorem` is the Lean analogue of a trusted
`ledger.add(theorem)` operation. -/
noncomputable def add (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (event : Event) (proof : Valid event) :
    Ledger.{uOccurrence, uEvent} Event Valid where
  residuals := {
    Occurrence := Sum ledger.residuals.Occurrence PUnit
    occurrences := by
      letI : FinEnum ledger.residuals.Occurrence :=
        ledger.residuals.occurrences
      infer_instance
    event
      | .inl occurrence => ledger.residuals.event occurrence
      | .inr _ => event }
  certified
    | .inl occurrence => ledger.certified occurrence
    | .inr _ => proof

@[simp] theorem add_event_old
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (event : Event) (proof : Valid event)
    (occurrence : ledger.residuals.Occurrence) :
    (ledger.add event proof).residuals.event (.inl occurrence) =
      ledger.residuals.event occurrence :=
  rfl

@[simp] theorem add_event_new
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (event : Event) (proof : Valid event)
    (occurrence : PUnit) :
    (ledger.add event proof).residuals.event (.inr occurrence) = event :=
  rfl

/-- Compose two proof branches without inspecting or deduplicating events. -/
noncomputable def append
    (left right : Ledger.{uOccurrence, uEvent} Event Valid) :
    Ledger.{uOccurrence, uEvent} Event Valid where
  residuals := left.residuals.append right.residuals
  certified
    | .inl occurrence => left.certified occurrence
    | .inr occurrence => right.certified occurrence

/-- A local producer theorem.  It contains only the problem-specific event
construction and the property proved about that event. -/
structure Producer (Input : Type uInput) where
  emit : Input → Event
  certified : ∀ input, Valid (emit input)

/-- Run one producer theorem over the exact graph-owned occurrence schedule.
The input occurrence type is reused definitionally; no output list is rebuilt
and no possible-input universe is enumerated. -/
noncomputable def produce {Input : Type uInput}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Event := Event) (Valid := Valid) Input) :
    Ledger.{uOccurrence, uEvent} Event Valid where
  residuals := inputs.map producer.emit
  certified := fun occurrence => producer.certified (inputs.event occurrence)

@[simp] theorem produce_event {Input : Type uInput}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Event := Event) (Valid := Valid) Input)
    (occurrence : inputs.Occurrence) :
    (produce inputs producer).residuals.event occurrence =
      producer.emit (inputs.event occurrence) :=
  rfl

theorem produce_certified {Input : Type uInput}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Event := Event) (Valid := Valid) Input)
    (occurrence : inputs.Occurrence) :
    Valid ((produce inputs producer).residuals.event occurrence) :=
  (produce inputs producer).certified occurrence

/-- Restrict an existing proof state to a decidable subfamily of actual
occurrences. -/
noncomputable def restrict
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (keep : ledger.residuals.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    Ledger.{uOccurrence, uEvent} Event Valid where
  residuals := ledger.residuals.restrict keep keepDecidable
  certified := fun occurrence => ledger.certified occurrence.1

/-- Transport a certified ledger through a theorem preserving its invariant. -/
noncomputable def map {Other : Type uOther} {OtherValid : Other → Prop}
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (f : Event → Other)
    (preserves : ∀ event, Valid event → OtherValid (f event)) :
    Ledger.{uOccurrence, uOther} Other OtherValid where
  residuals := ledger.residuals.map f
  certified := fun occurrence =>
    preserves (ledger.residuals.event occurrence) (ledger.certified occurrence)

/-- The only problem-specific part of a residual-to-consumer handoff: turn
the theorem attached to one event into the consumer's semantic seed. -/
structure SemanticAdapter where
  Seed : Event → Type uSeed
  adapt : ∀ event, Valid event → Seed event

/-- Attach consumer seeds to all existing occurrences.  Composition,
occurrence identity, and alignment with producer theorems are framework-owned.
The registered `Core.Routing.CTTransition` consumes these seeds afterwards. -/
noncomputable def routeSeeds
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (adapter : SemanticAdapter.{uEvent, uSeed}
      (Event := Event) (Valid := Valid)) :
    FiniteResidualLedger.Ledger.View.{uOccurrence, uEvent, uSeed}
      ledger.residuals where
  Payload := fun occurrence => adapter.Seed (ledger.residuals.event occurrence)
  value := fun occurrence => adapter.adapt _ (ledger.certified occurrence)

@[simp] theorem routeSeeds_value
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid)
    (adapter : SemanticAdapter.{uEvent, uSeed}
      (Event := Event) (Valid := Valid))
    (occurrence : ledger.residuals.Occurrence) :
    (ledger.routeSeeds adapter).value occurrence =
      adapter.adapt (ledger.residuals.event occurrence)
        (ledger.certified occurrence) :=
  rfl

/-- The automation performs one producer application per actual input
occurrence. -/
noncomputable def checks
    (ledger : Ledger.{uOccurrence, uEvent} Event Valid) : Nat :=
  ledger.residuals.checks

@[simp] theorem produce_checks {Input : Type uInput}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Event := Event) (Valid := Valid) Input) :
    (produce inputs producer).checks = inputs.checks :=
  rfl

end Ledger

end StructuralExhaustion.Core.CertifiedResidualLedger
