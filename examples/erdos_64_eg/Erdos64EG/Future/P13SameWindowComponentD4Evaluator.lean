import Erdos64EG.Future.P13SameWindowComponentD4EvaluatorConstructionResidual
import StructuralExhaustion.Graph.InducedPathComponentD4Evaluator

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Graph-owned D4 producer after node [194]

This module consumes the exact node-[194] construction residual.  Its
dependent marker determines the same component input and canonical path used
by the D1--D3 ledger, so the raw-wedge D4 family can be computed without any
caller-authored predicate.  The literal D5--D7 tail is retained.  No
compatible-context equality, CT8 removal, or node-[24] density fact is used.
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

inductive D4EvaluationOutput where
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
      (firstEvaluation : InducedPathComponentD4Evaluator.Evaluation
        b.routed.residual.repetition.firstInput PowerOfTwoLength
          powerOfTwoLengthDecidable fb)
      (secondEvaluation : InducedPathComponentD4Evaluator.Evaluation
        b.routed.residual.repetition.secondInput PowerOfTwoLength
          powerOfTwoLengthDecidable sb)
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

noncomputable def runD4Evaluation : transition.D4EvaluationOutput source174 := by
  cases transition.runD4EvaluatorConstruction source174 source175 source180
      source182 source185 source188 source191 source194 with
  | coarse b f s fc sc fr sr fx sx fb sb =>
      exact .coarse b f s fc sc fr sr fx sx fb sb
        (InducedPathComponentD4Evaluator.run
          b.routed.residual.repetition.firstInput PowerOfTwoLength
          powerOfTwoLengthDecidable fb)
        (InducedPathComponentD4Evaluator.run
          b.routed.residual.repetition.secondInput PowerOfTwoLength
          powerOfTwoLengthDecidable sb)
  | bounded b o oc orq ox build =>
      exact .bounded b o oc orq ox build
        (InducedPathComponentD4Evaluator.run
          (InducedPathComponentD1D3Ledger.connectorInput
            (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)
          PowerOfTwoLength powerOfTwoLengthDecidable build)

theorem runD4Evaluation_exhaustive :
    (∃ b f s fc sc fr sr fx sx fb sb fe se,
      transition.runD4Evaluation source174 source175 source180 source182
        source185 source188 source191 source194 =
          .coarse b f s fc sc fr sr fx sx fb sb fe se) ∨
    (∃ b o oc orq ox build evaluation,
      transition.runD4Evaluation source174 source175 source180 source182
        source185 source188 source191 source194 =
          .bounded b o oc orq ox build evaluation) := by
  cases equation : transition.runD4Evaluation source174 source175 source180
      source182 source185 source188 source191 source194 with
  | coarse b f s fc sc fr sr fx sx fb sb fe se =>
      exact Or.inl ⟨b, f, s, fc, sc, fr, sr, fx, sx, fb, sb, fe, se, rfl⟩
  | bounded b o oc orq ox build evaluation =>
      exact Or.inr ⟨b, o, oc, orq, ox, build, evaluation, rfl⟩

theorem runD4Evaluation_localWork :
    match transition.runD4Evaluation source174 source175 source180 source182
        source185 source188 source191 source194 with
    | .coarse b _ _ _ _ _ _ _ _ _ _ _ _ =>
        InducedPathComponentD4.visibleChecks
            b.routed.residual.repetition.firstInput +
          InducedPathComponentD4.visibleChecks
            b.routed.residual.repetition.secondInput ≤
          8 * ctx.G.object.input.vertices.card ^ 3
    | .bounded b _ _ _ _ _ _ =>
        InducedPathComponentD4.visibleChecks
          (InducedPathComponentD1D3Ledger.connectorInput
            (transition.d1d3LedgerInput source174)
              b.routed.residual.scan.row) ≤
          4 * ctx.G.object.input.vertices.card ^ 3 := by
  cases transition.runD4Evaluation source174 source175 source180 source182
      source185 source188 source191 source194 with
  | coarse b =>
      have first := InducedPathComponentD4Evaluator.visibleChecks_polynomial
        b.routed.residual.repetition.firstInput
      have second := InducedPathComponentD4Evaluator.visibleChecks_polynomial
        b.routed.residual.repetition.secondInput
      omega
  | bounded b =>
      exact InducedPathComponentD4Evaluator.visibleChecks_polynomial
        (InducedPathComponentD1D3Ledger.connectorInput
          (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
