import StructuralExhaustion.Core.FiniteProducedSupportLedger
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Graph.FiniteResidualSupportLedger

namespace StructuralExhaustion.Graph.ResidualSupportRefinement

open StructuralExhaustion

universe uOccurrence uEvent uVertex

/-!
# Accumulated graph-support residuals

This profile joins the persistent occurrence ledger, accumulated theorem
state, declared graph support, ordered first-hit recognition, and legacy list
materialization.  An application supplies only its event support function.
-/

variable {Event : Type uEvent}

/-- The graph-specific datum attached to an event language. -/
structure Profile (Vertex : Type uVertex) where
  vertexDecEq : DecidableEq Vertex
  support : Event → Finset Vertex

namespace Profile

variable {Vertex : Type uVertex}
variable {facts : List (Event → Prop)}

def Contains (profile : Profile (Event := Event) Vertex)
    (vertex : Vertex) (event : Event) : Prop :=
  vertex ∈ profile.support event

/-- The exact occurrence support view; equal event values at different
producer occurrences remain different scan positions. -/
noncomputable def view (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) :
    FiniteResidualSupportLedger.View ledger.residuals Vertex where
  vertexDecEq := profile.vertexDecEq
  support := fun occurrence =>
    profile.support (ledger.residuals.event occurrence)

/-- Framework-owned compatibility projection for a list-indexed consumer.
The list is definitionally the current occurrence order mapped through the
event function. -/
noncomputable def materialize
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) :
    Core.FiniteProducedSupportLedger.Ledger Event Vertex where
  entries := ledger.events
  vertexDecEq := profile.vertexDecEq
  support := profile.support

@[simp] theorem materialize_entries
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) :
    (profile.materialize ledger).entries = ledger.events :=
  rfl

theorem event_mem_materialize
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) (occurrence : ledger.residuals.Occurrence) :
    ledger.residuals.event occurrence ∈
      (profile.materialize ledger).entries :=
  ledger.event_mem_events occurrence

/-- A first graph-support hit together with the current accumulated theorem
state for that literal occurrence. -/
structure FirstHit (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) (vertex : Vertex) where
  raw : FiniteResidualSupportLedger.View.FirstHit
    (profile.view ledger) vertex

namespace FirstHit

variable {profile : Profile (Event := Event) Vertex}
variable {ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
  Event facts}
variable {vertex : Vertex}

abbrev occurrence (hit : FirstHit profile ledger vertex) := hit.raw.occurrence

def state (hit : FirstHit profile ledger vertex) :
    Core.ResidualRefinement.State Event facts :=
  ledger.state hit.occurrence

theorem contains (hit : FirstHit profile ledger vertex) :
    profile.Contains vertex hit.state.residual :=
  hit.raw.vertexMember

theorem occurrence_mem (hit : FirstHit profile ledger vertex) :
    hit.occurrence ∈ ledger.residuals.entries :=
  hit.raw.occurrence_mem (profile.view ledger) vertex

def get {property : Event → Prop}
    (hit : FirstHit profile ledger vertex)
    (position : Core.ResidualRefinement.Proofs.Member property facts) :
    property hit.state.residual :=
  hit.state.get position

/-- Enrich the hit state with the newly established support-membership fact;
all producer and earlier-node facts remain available. -/
def refined (hit : FirstHit profile ledger vertex) :
    Core.ResidualRefinement.State Event
      (profile.Contains vertex :: facts) :=
  hit.state.add (profile.Contains vertex) hit.contains

end FirstHit

/-- Ordered graph recognition retaining accumulated state on the hit branch
and an occurrence-total support absence theorem otherwise. -/
inductive Result (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) (vertex : Vertex) where
  | found : FirstHit profile ledger vertex → Result profile ledger vertex
  | absent : (∀ occurrence : ledger.residuals.Occurrence,
      vertex ∉ profile.support (ledger.residuals.event occurrence)) →
      Result profile ledger vertex

noncomputable def recognize
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) (vertex : Vertex) : Result profile ledger vertex :=
  match (profile.view ledger).recognize vertex with
  | .found hit => .found ⟨hit⟩
  | .absent absentProof => Result.absent absentProof

theorem recognize_exact
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) (vertex : Vertex) :
    match profile.recognize ledger vertex with
    | .found hit =>
        hit.occurrence ∈ ledger.residuals.entries ∧
          profile.Contains vertex hit.state.residual
    | .absent _ =>
        ∀ occurrence : ledger.residuals.Occurrence,
          vertex ∉ profile.support (ledger.residuals.event occurrence) := by
  unfold recognize
  cases result : (profile.view ledger).recognize vertex with
  | found hit => exact ⟨hit.occurrence_mem _ _, hit.vertexMember⟩
  | absent absentProof => exact absentProof

/-- One primitive support-membership check per actual occurrence. -/
noncomputable def checks
    (_profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) : Nat :=
  ledger.residuals.checks

@[simp] theorem checks_exact
    (profile : Profile (Event := Event) Vertex)
    (ledger : Core.ResidualRefinement.Ledger.{uOccurrence, uEvent}
      Event facts) :
    profile.checks ledger = ledger.residuals.occurrences.card :=
  ledger.residuals.checks_exact

end Profile

end StructuralExhaustion.Graph.ResidualSupportRefinement
