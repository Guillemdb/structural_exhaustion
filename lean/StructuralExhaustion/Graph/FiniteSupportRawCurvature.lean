import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.InducedPathAttachment

namespace StructuralExhaustion.Graph.FiniteSupportRawCurvature

open StructuralExhaustion

universe u v

variable {V : Type u} (object : FiniteObject V)
variable {Role : Type v} (roles : FinEnum Role)
variable (active : Finset V)

/-!
# Raw curvature on one finite active interface

This is the support-parametric form of declared coordinate D4.  It scans only
the vertices of the supplied active interface and ordered pairs of distinct
interface vertices.  A retained coordinate is an actual length-two wedge and
one already declared boundary role.  No ambient path, context, state, support,
or graph universe is generated.
-/

abbrev Vertex := {vertex : V // vertex ∈ active}

noncomputable def vertexDecidable (vertex : V) : Decidable (vertex ∈ active) := by
  letI : DecidableEq V := object.input.vertices.decEq
  infer_instance

@[implicit_reducible]
noncomputable def vertices : FinEnum (Vertex active) :=
  Core.Enumeration.subtype object.input.vertices
    (fun vertex => vertex ∈ active) (vertexDecidable object active)

abbrev EndpointPair := Core.Enumeration.OrderedDistinctPair (vertices object active)

@[implicit_reducible]
noncomputable def endpointPairs : FinEnum (EndpointPair object active) :=
  Core.Enumeration.orderedDistinctPairs (vertices object active)

abbrev Candidate := Vertex active × EndpointPair object active

def IsWedge (candidate : Candidate object active) : Prop :=
  object.graph.Adj candidate.1.1 candidate.2.1.1.1 ∧
    object.graph.Adj candidate.1.1 candidate.2.1.2.1

noncomputable def isWedgeDecidable (candidate : Candidate object active) :
    Decidable (IsWedge object active candidate) := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold IsWedge
  infer_instance

abbrev Wedge := {candidate : Candidate object active // IsWedge object active candidate}

@[implicit_reducible]
noncomputable def wedges : FinEnum (Wedge object active) :=
  Core.Enumeration.subtype
    (Core.Enumeration.prod (vertices object active) (endpointPairs object active))
    (IsWedge object active) (isWedgeDecidable object active)

namespace Wedge

variable {object active}

def center (wedge : Wedge object active) : V := wedge.1.1.1
def left (wedge : Wedge object active) : V := wedge.1.2.1.1.1
def right (wedge : Wedge object active) : V := wedge.1.2.1.2.1

theorem center_mem (wedge : Wedge object active) : wedge.center ∈ active := wedge.1.1.2
theorem left_mem (wedge : Wedge object active) : wedge.left ∈ active := wedge.1.2.1.1.2
theorem right_mem (wedge : Wedge object active) : wedge.right ∈ active := wedge.1.2.1.2.2
theorem adjacent_left (wedge : Wedge object active) :
    object.graph.Adj wedge.center wedge.left := wedge.2.1
theorem adjacent_right (wedge : Wedge object active) :
    object.graph.Adj wedge.center wedge.right := wedge.2.2

noncomputable def support (wedge : Wedge object active) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {wedge.left, wedge.center, wedge.right}

theorem support_subset (wedge : Wedge object active) : wedge.support ⊆ active := by
  intro vertex member
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact wedge.left_mem
  · exact wedge.center_mem
  · exact wedge.right_mem

end Wedge

abbrev Coordinate := Role × Wedge object active

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate (Role := Role) object active) :=
  Core.Enumeration.prod roles (wedges object active)

/-- Exact local value of one D4 coordinate.  Attachment labels are supplied by
the already selected boundary roles; the evaluator performs no search. -/
noncomputable def response (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (label : Role → V → InducedPathAttachment.Label 13)
    (coordinate : Coordinate (Role := Role) object active) : Bool :=
  decide (InducedPathAttachment.omegaTwo 13 LengthOK lengthOKDecidable
    (label coordinate.1 coordinate.2.left)
    (label coordinate.1 coordinate.2.center)
    (label coordinate.1 coordinate.2.right) = 1)

theorem response_true_iff (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (label : Role → V → InducedPathAttachment.Label 13)
    (coordinate : Coordinate (Role := Role) object active) :
    response object active LengthOK lengthOKDecidable label coordinate = true ↔
      InducedPathAttachment.omegaTwo 13 LengthOK lengthOKDecidable
        (label coordinate.1 coordinate.2.left)
        (label coordinate.1 coordinate.2.center)
        (label coordinate.1 coordinate.2.right) = 1 := by
  simp [response]

/-- Completeness is literal: every supported role/wedge label occurs in the
finite coordinate schedule. -/
theorem coordinate_mem (coordinate : Coordinate (Role := Role) object active) :
    coordinate ∈ (coordinates object roles active).orderedValues :=
  (coordinates object roles active).mem_orderedValues coordinate

/- Two adjacency decisions classify each raw triple, followed by at most one
response evaluation for every declared role.  The role factor must remain
visible in the generic API; only the Erdős two-boundary instantiation has
the specialized coefficient four. -/
noncomputable def visibleChecks : Nat :=
  (2 + roles.card) * active.card ^ 3

theorem active_card_le_vertices : active.card ≤ object.input.vertices.card := by
  rw [← object.card_vertexFinset]
  apply Finset.card_le_card
  intro vertex _member
  exact object.mem_vertexFinset vertex

theorem visibleChecks_le_cubic :
    visibleChecks roles active ≤
      (2 + roles.card) * object.input.vertices.card ^ 3 := by
  unfold visibleChecks
  exact Nat.mul_le_mul_left (2 + roles.card)
    (Nat.pow_le_pow_left (active_card_le_vertices object active) 3)

end StructuralExhaustion.Graph.FiniteSupportRawCurvature
