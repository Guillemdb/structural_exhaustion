import Erdos64EG.P13SameWindowComponentD4LocalClauseRequest
import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
universe u

/-! # Node [191]: missing graph-owned D4 evaluator residual

Node 188 supplies exact singleton requests but no predicate.  This node exposes
the missing graph-local predicate and provenance requirements without
accepting a Boolean.  Node 194 is the sole semantic successor.
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
variable (source175 : P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174)
variable (source180 : transition.D4D7SemanticReadinessSource source174 source175)
variable (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180)
variable (source185 : transition.D4D7ClauseCursorSource source174 source175 source180 source182)
variable (source188 : transition.D4LocalClauseRequestSource source174 source175
  source180 source182 source185)

structure D4EvaluatorResidualSource where
  node188 : transition.D4LocalClauseRequestOutput source174
  node188Exact : node188 = transition.runD4LocalClauseRequest source174 source175
    source180 source182 source185 source188

noncomputable def computedD4EvaluatorResidualSource :
    transition.D4EvaluatorResidualSource source174 source175 source180 source182
      source185 source188 where
  node188 := transition.runD4LocalClauseRequest source174 source175 source180
    source182 source185 source188
  node188Exact := rfl

inductive D4EvaluatorResidualOutput where
  | coarse
      (blocked : transition.D4D7CoarseSemanticBlock source174)
      (first : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.firstMissing)
      (second : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.secondMissing)
      (firstCursor : InducedPathComponentD4D7ClauseCursor.Cursor first)
      (secondCursor : InducedPathComponentD4D7ClauseCursor.Cursor second)
      (firstRequest : InducedPathComponentD4LocalClauseRequest.Request firstCursor)
      (secondRequest : InducedPathComponentD4LocalClauseRequest.Request secondCursor)
      (firstResidual : InducedPathComponentD4EvaluatorResidual.Residual firstRequest)
      (secondResidual : InducedPathComponentD4EvaluatorResidual.Residual secondRequest)
  | bounded
      (blocked : transition.D4D7BoundedSemanticBlock source174)
      (only : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.missing)
      (onlyCursor : InducedPathComponentD4D7ClauseCursor.Cursor only)
      (onlyRequest : InducedPathComponentD4LocalClauseRequest.Request onlyCursor)
      (onlyResidual : InducedPathComponentD4EvaluatorResidual.Residual onlyRequest)

noncomputable def runD4EvaluatorResidual
    (source191 : transition.D4EvaluatorResidualSource source174 source175
      source180 source182 source185 source188) :
    transition.D4EvaluatorResidualOutput source174 := by
  cases source191.node188 with
  | coarse blocked first second firstCursor secondCursor firstRequest secondRequest =>
      exact .coarse blocked first second firstCursor secondCursor firstRequest
        secondRequest (InducedPathComponentD4EvaluatorResidual.residual firstRequest)
        (InducedPathComponentD4EvaluatorResidual.residual secondRequest)
  | bounded blocked only onlyCursor onlyRequest =>
      exact .bounded blocked only onlyCursor onlyRequest
        (InducedPathComponentD4EvaluatorResidual.residual onlyRequest)

theorem d4EvaluatorResidual_exact_node188
    (source191 : transition.D4EvaluatorResidualSource source174 source175
      source180 source182 source185 source188) :
    source191.node188 = transition.runD4LocalClauseRequest source174 source175
      source180 source182 source185 source188 := source191.node188Exact

theorem runD4EvaluatorResidual_exhaustive
    (source191 : transition.D4EvaluatorResidualSource source174 source175
      source180 source182 source185 source188) :
    (∃ b f s fc sc fr sr fx sx,
      transition.runD4EvaluatorResidual source174 source175 source180 source182
        source185 source188 source191 = .coarse b f s fc sc fr sr fx sx) ∨
    (∃ b o oc orq ox,
      transition.runD4EvaluatorResidual source174 source175 source180 source182
        source185 source188 source191 = .bounded b o oc orq ox) := by
  cases equation : transition.runD4EvaluatorResidual source174 source175
      source180 source182 source185 source188 source191 with
  | coarse b f s fc sc fr sr fx sx =>
      exact Or.inl ⟨b, f, s, fc, sc, fr, sr, fx, sx, rfl⟩
  | bounded b o oc orq ox => exact Or.inr ⟨b, o, oc, orq, ox, rfl⟩

def D4EvaluatorResidualOutput.requiredInputs :
    transition.D4EvaluatorResidualOutput source174 → Nat
  | .coarse _ _ _ _ _ _ _ first second => first.needs.length + second.needs.length
  | .bounded _ _ _ _ only => only.needs.length

theorem runD4EvaluatorResidual_requiredInputs_le_four
    (source191 : transition.D4EvaluatorResidualSource source174 source175
      source180 source182 source185 source188) :
    (transition.runD4EvaluatorResidual source174 source175 source180 source182
      source185 source188 source191).requiredInputs ≤ 4 := by
  rcases source191 with ⟨node188, exact⟩
  cases node188 <;> simp [runD4EvaluatorResidual,
    D4EvaluatorResidualOutput.requiredInputs,
    InducedPathComponentD4EvaluatorResidual.residual,
    InducedPathComponentD4EvaluatorResidual.requirements]

theorem exists_verifiedD4EvaluatorResidualPrefix :
    ∃ output, output = transition.runD4EvaluatorResidual source174 source175
      source180 source182 source185 source188
      (transition.computedD4EvaluatorResidualSource source174 source175 source180
        source182 source185 source188) ∧
      ((∃ b f s fc sc fr sr fx sx, output = .coarse b f s fc sc fr sr fx sx) ∨
       (∃ b o oc orq ox, output = .bounded b o oc orq ox)) := by
  refine ⟨_, rfl, ?_⟩
  exact transition.runD4EvaluatorResidual_exhaustive source174 source175
    source180 source182 source185 source188 _

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
