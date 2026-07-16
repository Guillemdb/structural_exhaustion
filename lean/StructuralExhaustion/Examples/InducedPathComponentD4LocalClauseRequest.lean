import StructuralExhaustion.Examples.InducedPathComponentD4D7ClauseCursor
import StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest

namespace StructuralExhaustion.Examples.ComponentD4LocalClauseRequest

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def refined :=
  ComponentD4D7ClauseCursor.refined source LengthOK lengthOKDecidable

noncomputable def requested :=
  InducedPathComponentD4LocalClauseRequest.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
    (refined source LengthOK lengthOKDecidable)

theorem request_total : Nonempty
    (InducedPathComponentD4LocalClauseRequest.Requested source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (refined source LengthOK lengthOKDecidable)) :=
  InducedPathComponentD4LocalClauseRequest.run_total source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

example {Marker : Type} (marker : Nonempty Marker) :
    let ledger := InducedPathComponentD4D7ClauseSchedule.ledger marker
    let focused := InducedPathComponentD4D7ClauseCursor.cursor ledger
    let pending := InducedPathComponentD4LocalClauseRequest.request focused
    pending.slots = [.d4] ∧ pending.tail = [.d5, .d6, .d7] ∧
      pending.marker = marker := by
  simp [InducedPathComponentD4LocalClauseRequest.request,
    InducedPathComponentD4D7ClauseCursor.cursor,
    InducedPathComponentD4D7ClauseSchedule.ledger]

theorem local_requested_slots_le_two :
    InducedPathComponentD4LocalClauseRequest.requestedSlots source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (refined source LengthOK lengthOKDecidable) ≤ 2 :=
  InducedPathComponentD4LocalClauseRequest.requestedSlots_le_two source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

end StructuralExhaustion.Examples.ComponentD4LocalClauseRequest
