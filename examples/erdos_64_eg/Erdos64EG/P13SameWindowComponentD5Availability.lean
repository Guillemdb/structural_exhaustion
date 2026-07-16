import Erdos64EG.P13SameWindowComponentD4D7Support
import StructuralExhaustion.Graph.InducedPathComponentD5Availability
import StructuralExhaustion.Graph.InducedPathComponentHighCenterD5Decision

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Current same-marker D5 availability result

For each exact D4/D7-support marker this adapter first scans its literal active
support for a high center.  The high branch produces a same-support D6 center
input and its local incidence subfamily, without claiming D6 closure.
On the no-high branch, the minimum-degree-three baseline proves ambient
cubicity and the residual names exactly the still-missing P13-free and
internal-core-free facts.  No later node-63 support or node-24 density
conclusion is borrowed.
-/

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source174 : P13SameWindowComponentD1D3LedgerSource transition)
variable (source175 : P13SameWindowComponentD4D7OrCoarseRepeatSource
  transition source174)
variable (source180 : transition.D4D7SemanticReadinessSource source174 source175)
variable (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180)
variable (source185 : transition.D4D7ClauseCursorSource source174 source175
  source180 source182)
variable (source188 : transition.D4LocalClauseRequestSource source174 source175
  source180 source182 source185)
variable (source191 : transition.D4EvaluatorResidualSource source174 source175
  source180 source182 source185 source188)
variable (source194 : transition.D4EvaluatorConstructionSource source174 source175
  source180 source182 source185 source188 source191)

theorem componentMinimumDegreeThree : 3 ≤ ctx.G.object.minDegree :=
  (packedStaticInput.fixedContext ctx).baseline

abbrev CurrentD5Result
    {componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object}
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput
      PowerOfTwoLength powerOfTwoLengthDecidable build}
    (d7 : InducedPathComponentD4D7Evaluation.Evaluation (D7Stage ctx)
      componentInput PowerOfTwoLength powerOfTwoLengthDecidable d4) :=
  InducedPathComponentHighCenterD5Decision.Result (D7Stage ctx) componentInput
    PowerOfTwoLength powerOfTwoLengthDecidable d7
      (componentMinimumDegreeThree (ctx := ctx))

def D5Status : transition.D4D7SupportOutput source174 → Type (u + 1)
  | .coarse _b _f _s _fc _sc _fr _sr _fx _sx _fb _sb _fe _se fd7 sd7 =>
      CurrentD5Result (ctx := ctx) fd7 ×
        CurrentD5Result (ctx := ctx) sd7
  | .bounded _b _o _oc _orq _ox _build _evaluation d7 =>
      CurrentD5Result (ctx := ctx) d7

structure D5AvailabilityOutput where
  predecessor : transition.D4D7SupportOutput source174
  predecessorExact : predecessor = transition.runD4D7Support source174 source175
    source180 source182 source185 source188 source191 source194
  status : transition.D5Status source174 predecessor

noncomputable def runD5Availability :
    transition.D5AvailabilityOutput source174 source175 source180 source182
      source185 source188 source191 source194 := by
  let predecessor := transition.runD4D7Support source174 source175 source180
    source182 source185 source188 source191 source194
  refine { predecessor := predecessor, predecessorExact := rfl, status := ?_ }
  cases predecessor with
  | coarse b f s fc sc fr sr fx sx fb sb fe se fd7 sd7 =>
      exact
        (InducedPathComponentHighCenterD5Decision.run (D7Stage ctx)
          b.routed.residual.repetition.firstInput PowerOfTwoLength
            powerOfTwoLengthDecidable fd7 (componentMinimumDegreeThree (ctx := ctx)),
         InducedPathComponentHighCenterD5Decision.run (D7Stage ctx)
          b.routed.residual.repetition.secondInput PowerOfTwoLength
            powerOfTwoLengthDecidable sd7 (componentMinimumDegreeThree (ctx := ctx)))
  | bounded b o oc orq ox build evaluation d7 =>
      exact InducedPathComponentHighCenterD5Decision.run (D7Stage ctx)
        (InducedPathComponentD1D3Ledger.connectorInput
          (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)
        PowerOfTwoLength powerOfTwoLengthDecidable d7
          (componentMinimumDegreeThree (ctx := ctx))

/-- Every individual current marker takes one of the exact high-center or
no-high residual branches.  This exhaustive split is used in both constructors
of `runD5Availability`. -/
theorem currentHighCenterD5Result_exhaustive
    {componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object}
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput
      PowerOfTwoLength powerOfTwoLengthDecidable build}
    (d7 : InducedPathComponentD4D7Evaluation.Evaluation (D7Stage ctx)
      componentInput PowerOfTwoLength powerOfTwoLengthDecidable d4) :
    (∃ predecessor exact high,
      InducedPathComponentHighCenterD5Decision.run (D7Stage ctx)
        componentInput PowerOfTwoLength powerOfTwoLengthDecidable d7
          (componentMinimumDegreeThree (ctx := ctx)) =
        .high predecessor exact high) ∨
    (∃ residual,
      InducedPathComponentHighCenterD5Decision.run (D7Stage ctx)
        componentInput PowerOfTwoLength powerOfTwoLengthDecidable d7
          (componentMinimumDegreeThree (ctx := ctx)) = .noHigh residual) :=
  InducedPathComponentHighCenterD5Decision.run_exhaustive (D7Stage ctx)
    componentInput PowerOfTwoLength powerOfTwoLengthDecidable d7
      (componentMinimumDegreeThree (ctx := ctx))

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
