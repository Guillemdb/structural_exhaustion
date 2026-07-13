import MantelExample.Problem
import StructuralExhaustion.Graph.InducedPathAttachment

namespace MantelExample.CT10EdgeAttachment

open StructuralExhaustion

universe u

/-!
# CT10 transfer: attachments to an edge in a triangle-free graph

For Mantel's theorem, fix an edge as an induced path on two vertices.  A
third vertex cannot attach to both endpoints, since those three edges would
form a triangle.  Thus the two singleton endpoint labels are exactly the
legal nonempty attachment classes.  This file executes the same generic
compact-label classifier and graph attachment-cycle theorem used by the
Erdős `P₁₃` stage, on a four-candidate textbook instance.
-/

/-- The forbidden cycle length in the triangle-free formulation. -/
abbrev TriangleLength := Graph.TriangleLength

def triangleLengthDecidable (length : Nat) :
    Decidable (TriangleLength length) := by
  change Decidable (length = 3)
  infer_instance

abbrev EdgeLabel := Graph.InducedPathAttachment.Label 2
abbrev EdgeLabelCode := Graph.InducedPathAttachment.LabelCode 2

/-- Compact exact classifier for nonempty legal edge-attachment labels. -/
def edgeLabelProfile :
    CT10.ExhaustiveClassification.Profile EdgeLabelCode where
  candidates := Graph.InducedPathAttachment.labelCodes 2
  Accepts := fun code =>
    Graph.InducedPathAttachment.Legal 2 TriangleLength
      (Graph.InducedPathAttachment.decodeCode code)
  acceptsDecidable := fun code =>
    Graph.InducedPathAttachment.legalDecidable 2 TriangleLength
      triangleLengthDecidable
      (Graph.InducedPathAttachment.decodeCode code)

/-- The compact profile classifies exactly the graph-theoretic labels. -/
def edgeAttachmentClassification :
    Graph.InducedPathAttachment.Classification 2 TriangleLength where
  Candidate := EdgeLabelCode
  profile := edgeLabelProfile
  decode := Graph.InducedPathAttachment.labelCodeEquiv 2
  accepts_iff_legal := fun code => by
    change Graph.InducedPathAttachment.Legal 2 TriangleLength
        (Graph.InducedPathAttachment.decodeCode code) ↔
      Graph.InducedPathAttachment.Legal 2 TriangleLength
        ((Graph.InducedPathAttachment.labelCodeEquiv 2) code)
    rw [Graph.InducedPathAttachment.labelCodeEquiv_apply]

/-- All four subsets of the two edge positions are inspected. -/
theorem candidate_count : edgeLabelProfile.candidateCount = 4 := by
  native_decide

/-- The two singleton endpoint labels are the complete accepted table. -/
theorem legal_label_count : edgeLabelProfile.classCount = 2 := by
  native_decide

/-- Candidate classification, the CT10 direct scan, and row population use
ten primitive checks in total. -/
theorem check_count : edgeLabelProfile.checks = 10 := by
  rw [CT10.ExhaustiveClassification.Profile.checks,
    candidate_count, legal_label_count]
  norm_num

theorem checks_quadratic :
    edgeLabelProfile.checks ≤
      (edgeLabelProfile.candidateCount + 1) ^ 2 := by
  rw [check_count, candidate_count]
  norm_num

/-- Boolean form of the exact two-position acceptance decision. -/
def edgeLabelAcceptedBool (code : EdgeLabelCode) : Bool :=
  @decide (edgeLabelProfile.Accepts code)
    (edgeLabelProfile.acceptsDecidable code)

private theorem legal_label_card_computation :
    ∀ code : EdgeLabelCode, edgeLabelAcceptedBool code = true →
      (Graph.InducedPathAttachment.decodeCode code).card = 1 := by
  native_decide

/-- Every accepted label is a singleton, the familiar local observation in
the proof of Mantel's theorem. -/
theorem legal_label_card_eq_one (code : EdgeLabelCode)
    (accepted : edgeLabelProfile.Accepts code) :
    (Graph.InducedPathAttachment.decodeCode code).card = 1 := by
  apply legal_label_card_computation code
  simp [edgeLabelAcceptedBool, accepted]

/-- Execute the reusable CT10 classifier in an arbitrary finite graph's
branch context. -/
def verifiedStage {V : Type u} (object : Graph.FiniteObject V) :
    edgeLabelProfile.VerifiedStage (Graph.FiniteObject.context object) :=
  edgeLabelProfile.verifiedStage (Graph.FiniteObject.context object)

theorem run_terminal_exhaustive {V : Type u}
    (object : Graph.FiniteObject V) :
    (edgeLabelProfile.run (Graph.FiniteObject.context object)).terminal =
      .exhaustive :=
  (verifiedStage object).terminal

theorem run_trace_exact {V : Type u} (object : Graph.FiniteObject V) :
    (edgeLabelProfile.run (Graph.FiniteObject.context object)).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  (verifiedStage object).trace

theorem run_total {V : Type u} (object : Graph.FiniteObject V) :
    ∃ result : CT10.ExecutionResult
        (edgeLabelProfile.capability (Graph.FiniteObject.problem V))
        (edgeLabelProfile.input (Graph.FiniteObject.context object)),
      result.terminal = .exhaustive ∧
        result.trace =
          [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
        result.outcome.Valid ∧
        CT10.Graph.ValidTrace
          (edgeLabelProfile.capability (Graph.FiniteObject.problem V))
          (edgeLabelProfile.input (Graph.FiniteObject.context object))
          result.trace :=
  (verifiedStage object).total

/-- The same fact expressed through the compact CT10 candidate contract. -/
theorem actual_edge_attachment_accepted {V : Type u}
    (object : Graph.FiniteObject V)
    (triangleFree : object.graph.CliqueFree 3)
    (path : SimpleGraph.pathGraph 2 ↪g object.graph)
    (outside : V)
    (outsidePath : ∀ position : Fin 2, outside ≠ path position)
    (attached : ∃ position, object.graph.Adj outside (path position)) :
    edgeLabelProfile.Accepts
      ((Graph.InducedPathAttachment.labelCodeEquiv 2).symm
        (Graph.InducedPathAttachment.finiteObjectAttachmentLabel object path
          outside)) := by
  change Graph.InducedPathAttachment.Legal 2 TriangleLength
    (Graph.InducedPathAttachment.decodeCode
      ((Graph.InducedPathAttachment.labelCodeEquiv 2).symm
        (Graph.InducedPathAttachment.finiteObjectAttachmentLabel object path
          outside)))
  rw [← Graph.InducedPathAttachment.labelCodeEquiv_apply,
    Equiv.apply_symm_apply]
  exact Graph.InducedPathAttachment.finiteObjectEdgeAttachment_legal_of_cliqueFree
    object triangleFree path outside outsidePath attached

end MantelExample.CT10EdgeAttachment
