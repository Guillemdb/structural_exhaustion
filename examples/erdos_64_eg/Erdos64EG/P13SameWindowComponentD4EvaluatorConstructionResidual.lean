import Erdos64EG.P13SameWindowComponentD4EvaluatorResidual
import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual

namespace Erdos64EG.Internal
open StructuralExhaustion
open StructuralExhaustion.Graph
universe u

/-! # Node [194]: graph-owned D4 evaluator construction residual -/

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
variable (source175 : P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174)
variable (source180 : transition.D4D7SemanticReadinessSource source174 source175)
variable (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180)
variable (source185 : transition.D4D7ClauseCursorSource source174 source175 source180 source182)
variable (source188 : transition.D4LocalClauseRequestSource source174 source175 source180 source182 source185)
variable (source191 : transition.D4EvaluatorResidualSource source174 source175 source180 source182 source185 source188)

structure D4EvaluatorConstructionSource where
  node191 : transition.D4EvaluatorResidualOutput source174
  node191Exact : node191 = transition.runD4EvaluatorResidual source174 source175
    source180 source182 source185 source188 source191

noncomputable def computedD4EvaluatorConstructionSource :
    transition.D4EvaluatorConstructionSource source174 source175 source180
      source182 source185 source188 source191 :=
  ⟨transition.runD4EvaluatorResidual source174 source175 source180 source182
    source185 source188 source191, rfl⟩

inductive D4EvaluatorConstructionOutput where
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
      (fbuild : InducedPathComponentD4EvaluatorConstructionResidual.Residual fx)
      (sbuild : InducedPathComponentD4EvaluatorConstructionResidual.Residual sx)
  | bounded
      (b : transition.D4D7BoundedSemanticBlock source174)
      (o : InducedPathComponentD4D7ClauseSchedule.Ledger b.missing)
      (oc : InducedPathComponentD4D7ClauseCursor.Cursor o)
      (orq : InducedPathComponentD4LocalClauseRequest.Request oc)
      (ox : InducedPathComponentD4EvaluatorResidual.Residual orq)
      (build : InducedPathComponentD4EvaluatorConstructionResidual.Residual ox)

noncomputable def runD4EvaluatorConstruction
    (source194 : transition.D4EvaluatorConstructionSource source174 source175
      source180 source182 source185 source188 source191) :
    transition.D4EvaluatorConstructionOutput source174 := by
  cases source194.node191 with
  | coarse b f s fc sc fr sr fx sx =>
      exact .coarse b f s fc sc fr sr fx sx
        (InducedPathComponentD4EvaluatorConstructionResidual.residual fx)
        (InducedPathComponentD4EvaluatorConstructionResidual.residual sx)
  | bounded b o oc orq ox =>
      exact .bounded b o oc orq ox
        (InducedPathComponentD4EvaluatorConstructionResidual.residual ox)

theorem exact_node191
    (source194 : transition.D4EvaluatorConstructionSource source174 source175
      source180 source182 source185 source188 source191) :
    source194.node191 = transition.runD4EvaluatorResidual source174 source175
      source180 source182 source185 source188 source191 := source194.node191Exact

def D4EvaluatorConstructionOutput.requiredInputs :
    transition.D4EvaluatorConstructionOutput source174 → Nat
  | .coarse _ _ _ _ _ _ _ _ _ f s => f.inputs.length + s.inputs.length
  | .bounded _ _ _ _ _ only => only.inputs.length

theorem runD4EvaluatorConstruction_requiredInputs_le_six
    (source194 : transition.D4EvaluatorConstructionSource source174 source175
      source180 source182 source185 source188 source191) :
    (transition.runD4EvaluatorConstruction source174 source175 source180
      source182 source185 source188 source191 source194).requiredInputs ≤ 6 := by
  rcases source194 with ⟨node191, exact⟩
  cases node191 <;> simp [runD4EvaluatorConstruction,
    D4EvaluatorConstructionOutput.requiredInputs,
    InducedPathComponentD4EvaluatorConstructionResidual.residual,
    InducedPathComponentD4EvaluatorConstructionResidual.constructionInputs]

theorem runD4EvaluatorConstruction_exhaustive
    (source194 : transition.D4EvaluatorConstructionSource source174 source175
      source180 source182 source185 source188 source191) :
    (∃ b f s fc sc fr sr fx sx fb sb,
      transition.runD4EvaluatorConstruction source174 source175 source180
        source182 source185 source188 source191 source194 =
          .coarse b f s fc sc fr sr fx sx fb sb) ∨
    (∃ b o oc orq ox build,
      transition.runD4EvaluatorConstruction source174 source175 source180
        source182 source185 source188 source191 source194 =
          .bounded b o oc orq ox build) := by
  cases h : transition.runD4EvaluatorConstruction source174 source175 source180
      source182 source185 source188 source191 source194 with
  | coarse b f s fc sc fr sr fx sx fb sb =>
      exact Or.inl ⟨b,f,s,fc,sc,fr,sr,fx,sx,fb,sb,rfl⟩
  | bounded b o oc orq ox build => exact Or.inr ⟨b,o,oc,orq,ox,build,rfl⟩

theorem exists_verifiedD4EvaluatorConstructionPrefix :
    ∃ output, output = transition.runD4EvaluatorConstruction source174 source175
      source180 source182 source185 source188 source191
      (transition.computedD4EvaluatorConstructionSource source174 source175
        source180 source182 source185 source188 source191) := ⟨_, rfl⟩

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
