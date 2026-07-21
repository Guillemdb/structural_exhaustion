import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.InducedPathAttachment
import StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

namespace StructuralExhaustion.Graph.InducedPathComponentD4

open StructuralExhaustion
open InducedPathColdSkeleton
open InducedPathWindowLedger

universe u

variable {V : Type u} {object : FiniteObject V}
variable (input : InducedPathComponentBoundarySchedule.Input object)

/-!
# Graph-owned D4 coordinates on one component corridor

D4 is a finite coordinate family, not one caller-authored Boolean.  The
active support is the literal ambient image of the already computed shortest
component path.  A raw coordinate consists of one center and one canonically
ordered pair of distinct neighbours inside that support, together with one of
the two boundary-window roles.  Its value is the manuscript's `omegaTwo`
curvature relation on the three actual attachment labels for that boundary
window.

The enumeration scans only support vertices and their local pairs.  Outside
contexts and ambient state/graph families do not occur.
-/

noncomputable abbrev data :=
  InducedPathComponentD1D3Observation.data input

noncomputable abbrev canonicalPath :=
  InducedPathComponentD1D3Observation.canonicalPath input

/-- Ambient vertices occurring on the one stored component path. -/
noncomputable def activeSupport : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (InducedPathComponentBoundarySchedule.componentPath input).support.toFinset.image
    (fun vertex => vertex.1.1)

abbrev SupportVertex := {vertex : V // vertex ∈ activeSupport input}

noncomputable def supportVertexDecidable (vertex : V) :
    Decidable (vertex ∈ activeSupport input) := by
  letI : DecidableEq V := object.input.vertices.decEq
  infer_instance

@[implicit_reducible]
noncomputable def supportVertices : FinEnum (SupportVertex input) :=
  Core.Enumeration.subtype object.input.vertices
    (fun vertex => vertex ∈ activeSupport input) (supportVertexDecidable input)

abbrev EndpointPair :=
  Core.Enumeration.OrderedDistinctPair (supportVertices input)

@[implicit_reducible]
noncomputable def endpointPairs : FinEnum (EndpointPair input) :=
  Core.Enumeration.orderedDistinctPairs (supportVertices input)

abbrev Candidate := SupportVertex input × EndpointPair input

def IsInternalWedge (candidate : Candidate input) : Prop :=
  object.graph.Adj candidate.1.1 candidate.2.1.1.1 ∧
    object.graph.Adj candidate.1.1 candidate.2.1.2.1

noncomputable def isInternalWedgeDecidable (candidate : Candidate input) :
    Decidable (IsInternalWedge input candidate) := by
  unfold IsInternalWedge
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  infer_instance

abbrev Wedge := {candidate : Candidate input // IsInternalWedge input candidate}

@[implicit_reducible]
noncomputable def wedges : FinEnum (Wedge input) :=
  Core.Enumeration.subtype
    (Core.Enumeration.prod (supportVertices input) (endpointPairs input))
    (IsInternalWedge input) (isInternalWedgeDecidable input)

namespace Wedge

noncomputable def center (wedge : Wedge input) : V := wedge.1.1.1
noncomputable def left (wedge : Wedge input) : V := wedge.1.2.1.1.1
noncomputable def right (wedge : Wedge input) : V := wedge.1.2.1.2.1

theorem center_mem (wedge : Wedge input) :
    wedge.center ∈ activeSupport input := wedge.1.1.2

theorem left_mem (wedge : Wedge input) :
    wedge.left ∈ activeSupport input := wedge.1.2.1.1.2

theorem right_mem (wedge : Wedge input) :
    wedge.right ∈ activeSupport input := wedge.1.2.1.2.2

theorem left_ne_right (wedge : Wedge input) : wedge.left ≠ wedge.right := by
  intro equal
  have rankEqual := congrArg
    (fun vertex : SupportVertex input => (supportVertices input).equiv vertex)
    (Subtype.ext equal)
  exact (Nat.ne_of_lt wedge.1.2.2) (congrArg Fin.val rankEqual)

theorem adjacent_left (wedge : Wedge input) :
    object.graph.Adj wedge.center wedge.left := wedge.2.1

theorem adjacent_right (wedge : Wedge input) :
    object.graph.Adj wedge.center wedge.right := wedge.2.2

noncomputable def support (wedge : Wedge input) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {wedge.left, wedge.center, wedge.right}

theorem support_subset_active (wedge : Wedge input) :
    wedge.support ⊆ activeSupport input := by
  intro vertex member
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact wedge.left_mem
  · exact wedge.center_mem
  · exact wedge.right_mem

end Wedge

/-- One raw wedge evaluated relative to one of the two boundary windows. -/
abbrev Coordinate := Core.FixedTwoBoundaryCutState.BoundaryRole × Wedge input

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate input) := by
  exact Core.Enumeration.prod inferInstance (wedges input)

noncomputable def boundaryWindow
    (role : Core.FixedTwoBoundaryCutState.BoundaryRole) :
    WindowIndex object :=
  if role = 0 then input.anchor.window
  else (InducedPathComponentBoundarySchedule.twoStubComponent input).successor.window

noncomputable def attachmentLabel
    (role : Core.FixedTwoBoundaryCutState.BoundaryRole) (vertex : V) :
    InducedPathAttachment.Label 13 :=
  InducedPathAttachment.finiteObjectAttachmentLabel object
    (selectedWindow object (boundaryWindow input role)) vertex

/-- Literal D4 curvature value on the selected wedge and boundary window. -/
noncomputable def response (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (coordinate : Coordinate input) : Bool :=
  decide (InducedPathAttachment.omegaTwo 13 LengthOK lengthOKDecidable
    (attachmentLabel input coordinate.1 coordinate.2.left)
    (attachmentLabel input coordinate.1 coordinate.2.center)
    (attachmentLabel input coordinate.1 coordinate.2.right) = 1)

theorem response_true_iff (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (coordinate : Coordinate input) :
    response input LengthOK lengthOKDecidable coordinate = true ↔
      InducedPathAttachment.omegaTwo 13 LengthOK lengthOKDecidable
        (attachmentLabel input coordinate.1 coordinate.2.left)
        (attachmentLabel input coordinate.1 coordinate.2.center)
        (attachmentLabel input coordinate.1 coordinate.2.right) = 1 := by
  simp [response]

/-- The graph-owned D4 family fills the local-semantics interface for this
single clause.  D5--D7 are intentionally not folded into this alphabet. -/
noncomputable def semantics (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    TwoStubComponent.DeclaredLocalSemantics (data input) (canonicalPath input) where
  LocalCoordinate := Coordinate input
  coordinates := coordinates input
  localResponse := response input LengthOK lengthOKDecidable

/-- The normalized two-boundary cut-state obtained by evaluating the complete
D4 family on the exact D1--D3 component observation.  This is a projection of
the already stored component path; it does not scan a state or context
universe. -/
noncomputable def state (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    Core.FixedTwoBoundaryCutState.State 13 13 (Coordinate input) :=
  TwoStubComponent.fixedState LengthOK lengthOKDecidable
    (data input) (canonicalPath input)
    (semantics input LengthOK lengthOKDecidable)

theorem state_boundaryDegree (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (role : Core.FixedTwoBoundaryCutState.BoundaryRole) :
    (state input LengthOK lengthOKDecidable).boundaryDegree role =
      Core.FixedTwoBoundaryCutState.capDegree
        (if role = 0 then object.degree (data input).anchor.neighbor
        else object.degree (data input).successor.neighbor) := rfl

theorem state_windowOffset (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (role : Core.FixedTwoBoundaryCutState.BoundaryRole) :
    (state input LengthOK lengthOKDecidable).windowOffset role =
      (if role = 0 then (data input).anchor.offset
      else (data input).successor.offset) := rfl

theorem state_targetResponse (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (offset : Core.FixedTwoBoundaryCutState.TargetOffset 13) :
    (state input LengthOK lengthOKDecidable).targetResponse offset =
      decide (LengthOK ((canonicalPath input).path.length + offset.val)) := rfl

set_option maxHeartbeats 800000 in
theorem state_localResponse (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (coordinate : Coordinate input) :
    (state input LengthOK lengthOKDecidable).localResponse coordinate =
      response input LengthOK lengthOKDecidable coordinate := rfl

/-- Conservative full local-work envelope.  Each raw support triple uses at
most two adjacency decisions to classify an internal wedge, and each retained
wedge uses at most two response evaluations, one per boundary role. -/
noncomputable def visibleChecks : Nat := 4 * (activeSupport input).card ^ 3

theorem activeSupport_card_le_vertices :
    (activeSupport input).card ≤ object.input.vertices.card := by
  letI : DecidableEq V := object.input.vertices.decEq
  calc
    (activeSupport input).card ≤ object.vertexFinset.card := by
      apply Finset.card_le_card
      intro vertex member
      exact object.mem_vertexFinset vertex
    _ = object.input.vertices.card := object.card_vertexFinset

theorem visibleChecks_le_cubic :
    visibleChecks input ≤ 4 * object.input.vertices.card ^ 3 := by
  unfold visibleChecks
  exact Nat.mul_le_mul_left 4
    (Nat.pow_le_pow_left (activeSupport_card_le_vertices input) 3)

end StructuralExhaustion.Graph.InducedPathComponentD4
