import StructuralExhaustion.Graph.InducedPathComponentD4Evaluator

namespace StructuralExhaustion.Examples.InducedPathComponentD4Evaluator

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable (input : InducedPathComponentBoundarySchedule.Input object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)
variable
  {source : Nonempty (InducedPathComponentD4Evaluator.Marker input)}
  {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
  {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
  (request : InducedPathComponentD4Evaluator.Previous.Request focused)

noncomputable def pending :=
  InducedPathComponentD4EvaluatorConstructionResidual.residual
    (InducedPathComponentD4EvaluatorResidual.residual request)

noncomputable def evaluation :=
  InducedPathComponentD4Evaluator.run input LengthOK lengthOKDecidable
    (pending (input := input) request)

example : (evaluation (input := input) LengthOK lengthOKDecidable request).remaining =
    [InducedPathComponentD4D7ClauseSchedule.ClauseSlot.d5,
      .d6, .d7] :=
  (evaluation (input := input) LengthOK lengthOKDecidable request).tail_preserved

example : InducedPathComponentD4.visibleChecks input ≤
    4 * object.input.vertices.card ^ 3 :=
  InducedPathComponentD4Evaluator.visibleChecks_polynomial input

end StructuralExhaustion.Examples.InducedPathComponentD4Evaluator
