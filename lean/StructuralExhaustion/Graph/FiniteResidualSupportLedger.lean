import StructuralExhaustion.Core.FiniteResidualLedger

namespace StructuralExhaustion.Graph.FiniteResidualSupportLedger

open StructuralExhaustion

universe uOccurrence uEvent uVertex

variable {Event : Type uEvent}

/-- A graph-facing support view of an occurrence-indexed residual ledger.
Support belongs to an occurrence, not merely to its event value. -/
structure View
    (ledger : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event)
    (Vertex : Type uVertex) where
  vertexDecEq : DecidableEq Vertex
  support : ledger.Occurrence → Finset Vertex

namespace View

variable
  {ledger : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event}
  {Vertex : Type uVertex}

def Meets (view : View ledger Vertex)
    (vertex : Vertex) (occurrence : ledger.Occurrence) : Prop :=
  vertex ∈ view.support occurrence

noncomputable def meetsDecidable (view : View ledger Vertex)
    (vertex : Vertex) (occurrence : ledger.Occurrence) :
    Decidable (view.Meets vertex occurrence) := by
  letI : DecidableEq Vertex := view.vertexDecEq
  unfold Meets
  infer_instance

/-- Exact first support hit.  Both the occurrence and its event are retained;
`eventExact` prevents downstream code from replacing the producer output by
an equal-looking event from another occurrence. -/
structure FirstHit (view : View ledger Vertex) (vertex : Vertex) where
  before : List ledger.Occurrence
  occurrence : ledger.Occurrence
  event : Event
  eventExact : event = ledger.event occurrence
  after : List ledger.Occurrence
  split : ledger.entries = before ++ occurrence :: after
  vertexMember : vertex ∈ view.support occurrence
  beforeAbsent : ∀ earlier ∈ before, vertex ∉ view.support earlier

namespace FirstHit

theorem occurrence_mem (view : View ledger Vertex) (vertex : Vertex)
    (hit : FirstHit view vertex) :
    hit.occurrence ∈ ledger.entries := by
  rw [hit.split]
  simp

theorem exact_event (view : View ledger Vertex) (vertex : Vertex)
    (hit : FirstHit view vertex) :
    hit.event = ledger.event hit.occurrence :=
  hit.eventExact

end FirstHit

/-- Ordered recognition result with an occurrence-total absence branch. -/
inductive Result (view : View ledger Vertex) (vertex : Vertex) where
  | found (hit : FirstHit view vertex)
  | absent (none : ∀ occurrence : ledger.Occurrence,
      vertex ∉ view.support occurrence)

/-- Scan exactly the finite occurrence order and return the first support hit. -/
noncomputable def recognize (view : View ledger Vertex) (vertex : Vertex) :
    Result view vertex := by
  let search := Core.FiniteSearch.first ledger.occurrences
    (view.Meets vertex) (view.meetsDecidable vertex)
  cases search with
  | found hit =>
      exact .found {
        before := hit.before
        occurrence := hit.value
        event := ledger.event hit.value
        eventExact := rfl
        after := hit.after
        split := hit.split
        vertexMember := hit.holds
        beforeAbsent := hit.beforeAbsent }
  | absent none =>
      exact .absent fun occurrence =>
        none occurrence (ledger.occurrence_mem occurrence)

/-- Recognition is exact: a hit is the literal first occurrence and an
absence certificate quantifies every occurrence, including duplicate events. -/
theorem recognize_exact (view : View ledger Vertex) (vertex : Vertex) :
    match view.recognize vertex with
    | .found hit =>
        hit.event = ledger.event hit.occurrence ∧
        hit.occurrence ∈ ledger.entries ∧
        vertex ∈ view.support hit.occurrence ∧
        ∀ earlier ∈ hit.before, vertex ∉ view.support earlier
    | .absent _ =>
        ∀ occurrence : ledger.Occurrence,
          vertex ∉ view.support occurrence := by
  cases result : view.recognize vertex with
  | found hit =>
      exact ⟨hit.eventExact, hit.occurrence_mem view vertex,
        hit.vertexMember, hit.beforeAbsent⟩
  | absent absentProof => exact absentProof

theorem absent_all (view : View ledger Vertex) (vertex : Vertex)
    (none : ∀ occurrence : ledger.Occurrence,
      vertex ∉ view.support occurrence) :
    ∀ occurrence : ledger.Occurrence,
      vertex ∉ view.support occurrence :=
  none

/-- Restrict the support view to an exact decidable occurrence subtype. -/
noncomputable def restrict (view : View ledger Vertex)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    View (ledger.restrict keep keepDecidable) Vertex where
  vertexDecEq := view.vertexDecEq
  support := fun occurrence => view.support occurrence.1

@[simp] theorem restrict_support (view : View ledger Vertex)
    (keep : ledger.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence))
    (occurrence : (ledger.restrict keep keepDecidable).Occurrence) :
    (view.restrict keep keepDecidable).support occurrence =
      view.support occurrence.1 :=
  rfl

/-- Append two support views along the persistent tagged occurrence sum. -/
noncomputable def append
    {left right : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event}
    (leftView : View left Vertex) (rightView : View right Vertex) :
    View (left.append right) Vertex where
  vertexDecEq := leftView.vertexDecEq
  support
    | .inl occurrence => leftView.support occurrence
    | .inr occurrence => rightView.support occurrence

@[simp] theorem append_support_left
    {left right : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event}
    (leftView : View left Vertex) (rightView : View right Vertex)
    (occurrence : left.Occurrence) :
    (leftView.append rightView).support (.inl occurrence) =
      leftView.support occurrence :=
  rfl

@[simp] theorem append_support_right
    {left right : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event}
    (leftView : View left Vertex) (rightView : View right Vertex)
    (occurrence : right.Occurrence) :
    (leftView.append rightView).support (.inr occurrence) =
      rightView.support occurrence :=
  rfl

/-- Graph recognition performs one membership test per ledger occurrence. -/
noncomputable def checks (_view : View ledger Vertex) : Nat :=
  ledger.checks

@[simp] theorem checks_exact (view : View ledger Vertex) :
    view.checks = ledger.occurrences.card :=
  ledger.checks_exact

@[simp] theorem append_checks
    {left right : Core.FiniteResidualLedger.Ledger.{uOccurrence, uEvent} Event}
    (leftView : View left Vertex) (rightView : View right Vertex) :
    (leftView.append rightView).checks =
      leftView.checks + rightView.checks :=
  Core.FiniteResidualLedger.Ledger.append_checks left right

end View

end StructuralExhaustion.Graph.FiniteResidualSupportLedger
