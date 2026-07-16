import Erdos64EG.P13SameWindowComponentD4Evaluator
import Erdos64EG.CT15SparsePairResponses
import StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Same-marker component D4 and D7 support producer

This consumes the exact D4 evaluation and filters the already verified sparse
pair schedule onto that identical component support.  D5, D6, and the Boolean
semantics for D7 remain pending.  No response Boolean for D7,
compatible-context theorem, CT8 result, or node-[24] fact is asserted.
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

noncomputable abbrev D7Stage
    (ctx : Core.MinimalCounterexampleContext
      PackedProblem.{u} PackedTarget.{u}) :=
  sparsePairActivationStage ctx

inductive D4D7SupportOutput where
  | coarse
      (b : transition.D4D7CoarseSemanticBlock source174)
      (f : InducedPathComponentD4D7ClauseSchedule.Ledger b.firstMissing)
      (s : InducedPathComponentD4D7ClauseSchedule.Ledger b.secondMissing)
      (fc : InducedPathComponentD4D7ClauseCursor.Cursor f)
      (sc : InducedPathComponentD4D7ClauseCursor.Cursor s)
      (fr : InducedPathComponentD4LocalClauseRequest.Request fc)
      (sr : InducedPathComponentD4LocalClauseRequest.Request sc)
      (fx : InducedPathComponentD4EvaluatorResidual.Residual fr)
      (sx : InducedPathComponentD4EvaluatorResidual.Residual sr)
      (fb : InducedPathComponentD4EvaluatorConstructionResidual.Residual fx)
      (sb : InducedPathComponentD4EvaluatorConstructionResidual.Residual sx)
      (fe : InducedPathComponentD4Evaluator.Evaluation
        b.routed.residual.repetition.firstInput PowerOfTwoLength
          powerOfTwoLengthDecidable fb)
      (se : InducedPathComponentD4Evaluator.Evaluation
        b.routed.residual.repetition.secondInput PowerOfTwoLength
          powerOfTwoLengthDecidable sb)
      (fd7 : InducedPathComponentD4D7Evaluation.Evaluation
        (D7Stage ctx) b.routed.residual.repetition.firstInput PowerOfTwoLength
          powerOfTwoLengthDecidable fe)
      (sd7 : InducedPathComponentD4D7Evaluation.Evaluation
        (D7Stage ctx) b.routed.residual.repetition.secondInput PowerOfTwoLength
          powerOfTwoLengthDecidable se)
  | bounded
      (b : transition.D4D7BoundedSemanticBlock source174)
      (o : InducedPathComponentD4D7ClauseSchedule.Ledger b.missing)
      (oc : InducedPathComponentD4D7ClauseCursor.Cursor o)
      (orq : InducedPathComponentD4LocalClauseRequest.Request oc)
      (ox : InducedPathComponentD4EvaluatorResidual.Residual orq)
      (build : InducedPathComponentD4EvaluatorConstructionResidual.Residual ox)
      (evaluation : InducedPathComponentD4Evaluator.Evaluation
        (InducedPathComponentD1D3Ledger.connectorInput
          (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)
        PowerOfTwoLength powerOfTwoLengthDecidable build)
      (d7 : InducedPathComponentD4D7Evaluation.Evaluation (D7Stage ctx)
        (InducedPathComponentD1D3Ledger.connectorInput
          (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)
        PowerOfTwoLength powerOfTwoLengthDecidable evaluation)

noncomputable def runD4D7Support : transition.D4D7SupportOutput source174 := by
  cases transition.runD4Evaluation source174 source175 source180 source182
      source185 source188 source191 source194 with
  | coarse b f s fc sc fr sr fx sx fb sb fe se =>
      exact .coarse b f s fc sc fr sr fx sx fb sb fe se
        (InducedPathComponentD4D7Evaluation.run (D7Stage ctx)
          b.routed.residual.repetition.firstInput PowerOfTwoLength
            powerOfTwoLengthDecidable fe)
        (InducedPathComponentD4D7Evaluation.run (D7Stage ctx)
          b.routed.residual.repetition.secondInput PowerOfTwoLength
            powerOfTwoLengthDecidable se)
  | bounded b o oc orq ox build evaluation =>
      exact .bounded b o oc orq ox build evaluation
        (InducedPathComponentD4D7Evaluation.run (D7Stage ctx)
          (InducedPathComponentD1D3Ledger.connectorInput
            (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)
          PowerOfTwoLength powerOfTwoLengthDecidable evaluation)

theorem runD4D7Support_exhaustive :
    (∃ b f s fc sc fr sr fx sx fb sb fe se fd7 sd7,
      transition.runD4D7Support source174 source175 source180 source182
        source185 source188 source191 source194 =
          .coarse b f s fc sc fr sr fx sx fb sb fe se fd7 sd7) ∨
    (∃ b o oc orq ox build evaluation d7,
      transition.runD4D7Support source174 source175 source180 source182
        source185 source188 source191 source194 =
          .bounded b o oc orq ox build evaluation d7) := by
  cases equation : transition.runD4D7Support source174 source175 source180
      source182 source185 source188 source191 source194 with
  | coarse b f s fc sc fr sr fx sx fb sb fe se fd7 sd7 =>
      exact Or.inl ⟨b, f, s, fc, sc, fr, sr, fx, sx, fb, sb, fe, se,
        fd7, sd7, rfl⟩
  | bounded b o oc orq ox build evaluation d7 =>
      exact Or.inr ⟨b, o, oc, orq, ox, build, evaluation, d7, rfl⟩

/-- Every connected D7 schedule is bounded by the already verified quartic
sparse-pair schedule on the identical minimal context. -/
theorem componentD7_schedule_quartic
    (componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object) :
    (InducedPathComponentD7.coordinates (D7Stage ctx) componentInput).card ≤
      ctx.G.object.input.vertices.card ^ 4 := by
  have localLe := InducedPathComponentD4D7Evaluation.d7Checks_le_freePairs
    (D7Stage ctx) componentInput
  have partition := sparsePair_exact_partition ctx
  have freeLe :
      (SurplusPairResponse.freePairEnumeration (D7Stage ctx)).card ≤
        (SurplusPairResponse.pairEnumeration
          (setup := surplusPortActivationSetup ctx)).card := by
    change
      (SurplusPairResponse.freePairEnumeration
        (sparsePairActivationStage ctx)).card ≤
      (SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card
    omega
  exact localLe.trans (freeLe.trans (sparsePair_schedule_quartic ctx))

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
