import StructuralExhaustion.Graph.InducedPathComponentD4Evaluator
import StructuralExhaustion.Graph.InducedPathComponentD7

namespace StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation

open StructuralExhaustion

universe u

/-!
# Same-marker D4 evaluation and D7 support connection

Clause D7 is independently support-indexed.  Once the exact node-194 marker
has fixed the component input, the already verified sparse-pair schedule can
therefore be filtered to coordinates whose literal support is contained in
that component's active interface.  This connection does not require D5, D6,
full-response equivalence, or a density premise.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

namespace D4
export InducedPathComponentD4Evaluator (Evaluation)
end D4

/-- Output after connecting the D7 support schedule to the exact D4-evaluated
component marker.  The original D5--D7 tail remains pending: enumerating D7
supports does not supply its Boolean semantics. -/
structure Evaluation
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    (d4 : D4.Evaluation componentInput LengthOK lengthOKDecidable build) where
  predecessor : D4.Evaluation componentInput LengthOK lengthOKDecidable build
  predecessorExact : predecessor = d4
  d7Coordinates : FinEnum (InducedPathComponentD7.Coordinate stage componentInput)
  d7CoordinatesExact : d7Coordinates =
    InducedPathComponentD7.coordinates stage componentInput
  originalTail : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  originalTailExact : originalTail = [.d5, .d6, .d7]
  pendingTail : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  pendingTailExact : pendingTail = [.d5, .d6, .d7]

noncomputable def run
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    (d4 : D4.Evaluation componentInput LengthOK lengthOKDecidable build) :
    Evaluation stage componentInput LengthOK lengthOKDecidable d4 where
  predecessor := d4
  predecessorExact := rfl
  d7Coordinates := InducedPathComponentD7.coordinates stage componentInput
  d7CoordinatesExact := rfl
  originalTail := d4.remaining
  originalTailExact := d4.remainingExact
  pendingTail := [.d5, .d6, .d7]
  pendingTailExact := rfl

namespace Evaluation

variable {stage componentInput LengthOK lengthOKDecidable}
variable {source : Nonempty
  (InducedPathComponentD4Evaluator.Marker componentInput)}
variable {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
variable {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
variable {request : InducedPathComponentD4Evaluator.Previous.Request focused}
variable {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
variable {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
  evaluatorPending}
variable {d4 : D4.Evaluation componentInput LengthOK lengthOKDecidable build}

theorem coordinate_support_subset
    (_evaluation : Evaluation stage componentInput LengthOK lengthOKDecidable d4)
    (coordinate : InducedPathComponentD7.Coordinate stage componentInput) :
    coordinate.support stage componentInput ⊆
      InducedPathComponentD4.activeSupport componentInput :=
  coordinate.support_subset_active stage componentInput

theorem pending_tail_exact
    (evaluation : Evaluation stage componentInput LengthOK lengthOKDecidable d4) :
    evaluation.pendingTail = [.d5, .d6, .d7] :=
  evaluation.pendingTailExact

end Evaluation

/-- The D7 connection scans a subfamily of the existing finite free-pair
schedule and never enlarges it. -/
theorem d7Checks_le_freePairs :
    (InducedPathComponentD7.coordinates stage componentInput).card ≤
      (SurplusPairResponse.freePairEnumeration stage).card :=
  InducedPathComponentD7.coordinates_card_le_freePairs stage componentInput

end StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation
