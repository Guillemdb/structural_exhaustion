import StructuralExhaustion.Examples.InducedPathComponentD4LocalClauseRequest
import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual

namespace StructuralExhaustion.Examples.ComponentD4EvaluatorResidual

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u
variable {V : Type u} {object : FiniteObject V}
variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def requested :=
  ComponentD4LocalClauseRequest.requested source LengthOK lengthOKDecidable

noncomputable def exposed :=
  InducedPathComponentD4EvaluatorResidual.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
    (requested source LengthOK lengthOKDecidable)

theorem exposure_total : Nonempty
    (InducedPathComponentD4EvaluatorResidual.Exposed source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (requested source LengthOK lengthOKDecidable)) :=
  InducedPathComponentD4EvaluatorResidual.run_total source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

example {Marker : Type} (marker : Nonempty Marker) :
    let ledger := InducedPathComponentD4D7ClauseSchedule.ledger marker
    let cursor := InducedPathComponentD4D7ClauseCursor.cursor ledger
    let request := InducedPathComponentD4LocalClauseRequest.request cursor
    let residual := InducedPathComponentD4EvaluatorResidual.residual request
    residual.slots = [.d4] ∧ residual.tail = [.d5, .d6, .d7] ∧
      residual.needs = [.graphLocalPredicate, .predicateProvenance] := by
  simp [InducedPathComponentD4EvaluatorResidual.residual,
    InducedPathComponentD4EvaluatorResidual.requirements,
    InducedPathComponentD4LocalClauseRequest.request,
    InducedPathComponentD4D7ClauseCursor.cursor]

theorem local_required_inputs_le_four :
    InducedPathComponentD4EvaluatorResidual.requiredInputs source.input
      (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
      (requested source LengthOK lengthOKDecidable) ≤ 4 :=
  InducedPathComponentD4EvaluatorResidual.requiredInputs_le_four source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

end StructuralExhaustion.Examples.ComponentD4EvaluatorResidual
