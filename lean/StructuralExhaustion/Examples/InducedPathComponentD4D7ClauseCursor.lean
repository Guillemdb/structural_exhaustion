import StructuralExhaustion.Examples.InducedPathComponentD4D7ClauseSchedule
import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor

namespace StructuralExhaustion.Examples.ComponentD4D7ClauseCursor

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def scheduled :=
  ComponentD4D7ClauseSchedule.scheduled source LengthOK lengthOKDecidable

noncomputable def refined :=
  InducedPathComponentD4D7ClauseCursor.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
    (scheduled source LengthOK lengthOKDecidable)

theorem refinement_total : Nonempty
    (InducedPathComponentD4D7ClauseCursor.Refined source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (scheduled source LengthOK lengthOKDecidable)) :=
  InducedPathComponentD4D7ClauseCursor.run_total source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

example {Marker : Type} (marker : Nonempty Marker) :
    let ledger := InducedPathComponentD4D7ClauseSchedule.ledger marker
    let focused := InducedPathComponentD4D7ClauseCursor.cursor ledger
    focused.current = .d4 ∧ focused.remaining = [.d5, .d6, .d7] ∧
      ledger.slots = focused.current :: focused.remaining := by
  simp [InducedPathComponentD4D7ClauseCursor.cursor,
    InducedPathComponentD4D7ClauseSchedule.ledger,
    InducedPathComponentD4D7ClauseSchedule.clauseOrder]

theorem local_remaining_slots_le_six :
    InducedPathComponentD4D7ClauseCursor.remainingSlots source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (scheduled source LengthOK lengthOKDecidable) ≤ 6 :=
  InducedPathComponentD4D7ClauseCursor.remainingSlots_le_six source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

end StructuralExhaustion.Examples.ComponentD4D7ClauseCursor
