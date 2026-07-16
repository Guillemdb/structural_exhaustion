import StructuralExhaustion.Examples.InducedPathComponentD4D7SemanticReadiness
import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule

namespace StructuralExhaustion.Examples.ComponentD4D7ClauseSchedule

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def readiness :=
  ComponentD4D7SemanticReadiness.result source LengthOK lengthOKDecidable

noncomputable def scheduled :=
  InducedPathComponentD4D7ClauseSchedule.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
    (readiness source LengthOK lengthOKDecidable)

theorem schedule_total : Nonempty
    (InducedPathComponentD4D7ClauseSchedule.Scheduled source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (readiness source LengthOK lengthOKDecidable)) :=
  InducedPathComponentD4D7ClauseSchedule.run_total source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

example {Marker : Type} (marker : Nonempty Marker) :
    (InducedPathComponentD4D7ClauseSchedule.ledger marker).marker = marker ∧
      (InducedPathComponentD4D7ClauseSchedule.ledger marker).slots =
        InducedPathComponentD4D7ClauseSchedule.clauseOrder ∧
      (InducedPathComponentD4D7ClauseSchedule.ledger marker).slots.Nodup :=
  ⟨rfl, rfl, InducedPathComponentD4D7ClauseSchedule.clauseOrder_nodup⟩

theorem local_slots_le_eight :
    InducedPathComponentD4D7ClauseSchedule.emittedSlots source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (readiness source LengthOK lengthOKDecidable) ≤ 8 :=
  InducedPathComponentD4D7ClauseSchedule.emittedSlots_le_eight source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

end StructuralExhaustion.Examples.ComponentD4D7ClauseSchedule
