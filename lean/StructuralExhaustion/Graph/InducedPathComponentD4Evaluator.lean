import StructuralExhaustion.Graph.InducedPathComponentD4
import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual

namespace StructuralExhaustion.Graph.InducedPathComponentD4Evaluator

open StructuralExhaustion
open InducedPathColdSkeleton

universe u

/-!
# Graph-owned evaluator for one pending component D4 request

The predecessor marker is dependently indexed by the exact component input
and its canonical path.  Consequently it supplies the component-local data
without a caller-selected graph, path, or Boolean.  The evaluator below uses
the existing raw-wedge D4 family on that exact input and retains the literal
`[D5,D6,D7]` tail unchanged.

This is only the D4 coordinate producer.  It does not assert equality of full
responses, construct a replacement, execute CT8, or inspect any compatible
context family.
-/

variable {V : Type u} {object : FiniteObject V}
variable (input : InducedPathComponentBoundarySchedule.Input object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

abbrev Marker := TwoStubComponent.MissingD4D7Reconstruction
  (InducedPathComponentD1D3Observation.data input)
  (InducedPathComponentD1D3Observation.canonicalPath input)

namespace Previous

export InducedPathComponentD4D7ClauseSchedule (Ledger ClauseSlot)
export InducedPathComponentD4D7ClauseCursor (Cursor)
export InducedPathComponentD4LocalClauseRequest (Request)
export InducedPathComponentD4EvaluatorResidual (Residual)

end Previous

/-- Exact output of evaluating the focused D4 request from its dependent
component marker.  The response is definitionally the graph-owned raw-wedge
response, never caller data. -/
structure Evaluation
    {source : Nonempty (Marker input)}
    {ledger : Previous.Ledger source}
    {focused : Previous.Cursor ledger}
    {request : Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    (build :
      InducedPathComponentD4EvaluatorConstructionResidual.Residual
        evaluatorPending) where
  predecessor :
    InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending
  predecessorExact : predecessor = build
  componentInput : InducedPathComponentBoundarySchedule.Input object
  componentInputExact : componentInput = input
  semantics : TwoStubComponent.DeclaredLocalSemantics
    (InducedPathComponentD1D3Observation.data input)
    (InducedPathComponentD1D3Observation.canonicalPath input)
  semanticsExact : semantics =
    InducedPathComponentD4.semantics input LengthOK lengthOKDecidable
  requestedSlot : Previous.ClauseSlot
  requestedSlotExact : requestedSlot = .d4
  remaining : List Previous.ClauseSlot
  remainingExact : remaining = [.d5, .d6, .d7]

/-- Execute the D4 producer on the exact component indexed by the marker. -/
noncomputable def run
    {source : Nonempty (Marker input)}
    {ledger : Previous.Ledger source}
    {focused : Previous.Cursor ledger}
    {request : Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    (build :
      InducedPathComponentD4EvaluatorConstructionResidual.Residual
        evaluatorPending) :
    Evaluation input LengthOK lengthOKDecidable build where
  predecessor := build
  predecessorExact := rfl
  componentInput := input
  componentInputExact := rfl
  semantics := InducedPathComponentD4.semantics input LengthOK lengthOKDecidable
  semanticsExact := rfl
  requestedSlot := focused.current
  requestedSlotExact := request.slotIsD4
  remaining := request.tail
  remainingExact := request.tailIsD5D7

namespace Evaluation

variable {input LengthOK lengthOKDecidable}
variable {source : Nonempty (Marker input)}
variable {ledger : Previous.Ledger source}
variable {focused : Previous.Cursor ledger}
variable {request : Previous.Request focused}
variable {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
variable {pending :
  InducedPathComponentD4EvaluatorConstructionResidual.Residual
    evaluatorPending}

/-- Predicate provenance: every produced Boolean is the literal D4 curvature
test on its stored boundary role and internal wedge. -/
theorem semantics_and_response_provenance
    (evaluation : Evaluation input LengthOK lengthOKDecidable pending)
    (coordinate : InducedPathComponentD4.Coordinate input) :
    evaluation.semantics =
        InducedPathComponentD4.semantics input LengthOK lengthOKDecidable ∧
      (InducedPathComponentD4.response input LengthOK lengthOKDecidable
          coordinate = true ↔
        InducedPathAttachment.omegaTwo 13 LengthOK lengthOKDecidable
        (InducedPathComponentD4.attachmentLabel input coordinate.1
          coordinate.2.left)
        (InducedPathComponentD4.attachmentLabel input coordinate.1
          coordinate.2.center)
        (InducedPathComponentD4.attachmentLabel input coordinate.1
          coordinate.2.right) = 1) := by
  exact ⟨evaluation.semanticsExact,
    InducedPathComponentD4.response_true_iff input LengthOK
      lengthOKDecidable coordinate⟩

theorem tail_preserved
    (evaluation : Evaluation input LengthOK lengthOKDecidable pending) :
    evaluation.remaining = [.d5, .d6, .d7] :=
  evaluation.remainingExact

end Evaluation

/-- The local computation enumerates only actual support wedges and is cubic
in the ambient declared vertex count. -/
theorem visibleChecks_polynomial :
    InducedPathComponentD4.visibleChecks input ≤
      4 * object.input.vertices.card ^ 3 :=
  InducedPathComponentD4.visibleChecks_le_cubic input

end StructuralExhaustion.Graph.InducedPathComponentD4Evaluator
