import StructuralExhaustion.Core.CertifiedResidualLedger
import StructuralExhaustion.Graph.FiniteResidualSupportLedger

namespace StructuralExhaustion.Graph.CertifiedResidualSupportLedger

open StructuralExhaustion

universe uOccurrence uEvent uVertex

variable {Event : Type uEvent} {Valid : Event → Prop}

/-- Thin graph specialization: problem code supplies only the declared support
of one event type. -/
structure Profile (Vertex : Type uVertex) where
  vertexDecEq : DecidableEq Vertex
  support : Event → Finset Vertex

namespace Profile

noncomputable def view (profile : Profile (Event := Event) Vertex)
    (ledger : Core.CertifiedResidualLedger.Ledger.{uOccurrence, uEvent}
      Event Valid) :
    FiniteResidualSupportLedger.View ledger.residuals Vertex where
  vertexDecEq := profile.vertexDecEq
  support := fun occurrence => profile.support (ledger.residuals.event occurrence)

/-- Exact support recognition over actual theorem-producing occurrences. -/
noncomputable def recognize (profile : Profile (Event := Event) Vertex)
    (ledger : Core.CertifiedResidualLedger.Ledger.{uOccurrence, uEvent}
      Event Valid) (vertex : Vertex) :=
  (profile.view ledger).recognize vertex

theorem recognize_exact (profile : Profile (Event := Event) Vertex)
    (ledger : Core.CertifiedResidualLedger.Ledger.{uOccurrence, uEvent}
      Event Valid) (vertex : Vertex) :
    match profile.recognize ledger vertex with
    | .found hit =>
        hit.event = ledger.residuals.event hit.occurrence ∧
          hit.occurrence ∈ ledger.residuals.entries ∧
          vertex ∈ profile.support
            (ledger.residuals.event hit.occurrence) ∧
          Valid (ledger.residuals.event hit.occurrence)
    | .absent _ =>
        ∀ occurrence : ledger.residuals.Occurrence,
          vertex ∉ profile.support (ledger.residuals.event occurrence) := by
  unfold recognize
  cases result : (profile.view ledger).recognize vertex with
  | found hit =>
      exact ⟨hit.eventExact,
        hit.occurrence_mem (profile.view ledger) vertex,
        hit.vertexMember, ledger.certified hit.occurrence⟩
  | absent none => exact none

end Profile

end StructuralExhaustion.Graph.CertifiedResidualSupportLedger
