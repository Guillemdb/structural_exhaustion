import Hypostructure.Graph.BoundaryOverlap

/-!
# Boundary-overlap fixture

Two boundary edges are supplied by the piece and one by the context.  Their
single common edge exercises unrestricted-gluing inclusion--exclusion.  A
smaller replacement retains that overlap and therefore transfers strict local
progress through the fixed context.
-/

namespace Hypostructure.Fixtures.GraphBoundaryOverlap

open Hypostructure.Graph

def boundary : Boundary where
  Vertex := Fin 3
  vertices := inferInstance

def v0 : boundary.Vertex := ⟨0, by decide⟩
def v1 : boundary.Vertex := ⟨1, by decide⟩
def v2 : boundary.Vertex := ⟨2, by decide⟩

def source : BoundaryPiece boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := SimpleGraph.fromRel fun left right =>
    (left = .inl v0 ∧ right = .inl v1) ∨
    (left = .inl v1 ∧ right = .inl v2) ∨
    (left = .inl v0 ∧ right = .inr ())
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

def replacement : BoundaryPiece boundary where
  Internal := Empty
  internalVertices := inferInstance
  graph := SimpleGraph.fromRel fun left right =>
    (left = .inl v0 ∧ right = .inl v1) ∨
    (left = .inl v1 ∧ right = .inl v2)
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

def outside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := SimpleGraph.fromRel fun left right =>
    (left = .inl v0 ∧ right = .inl v1) ∨
    (left = .inl v2 ∧ right = .inr ())
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

theorem overlapEdgeCount_source :
    boundaryOverlapEdgeCount source outside = 1 := by
  decide

theorem overlapEdgeCount_replacement :
    boundaryOverlapEdgeCount replacement outside = 1 := by
  decide

theorem overlapDegree_source_v0 :
    boundaryOverlapDegree source outside v0 = 1 := by
  decide

theorem source_edge_inclusion_exclusion :
    (glue source outside).edgeCount + 1 =
      source.edgeCount + outside.pack.edgeCount := by
  simpa [overlapEdgeCount_source] using glue_edgeCount_add_overlap source outside

theorem source_boundary_zero_inclusion_exclusion :
    (glue source outside).degree (.inl v0) + 1 =
      source.boundaryDegree v0 + outside.ownedBoundaryDegree v0 := by
  simpa [overlapDegree_source_v0] using
    glue_boundaryDegree_add_overlap source outside v0

theorem replacement_locallySmaller :
    replacement.LocallySmaller source := by
  rw [BoundaryPiece.locallySmaller_iff]
  left
  decide

theorem overlapCount_agrees :
    boundaryOverlapEdgeCount replacement outside =
      boundaryOverlapEdgeCount source outside := by
  rw [overlapEdgeCount_replacement, overlapEdgeCount_source]

theorem replacement_glue_smaller :
    (glue replacement outside).LexicographicallySmaller
      (glue source outside) :=
  glue_lexicographicallySmaller_of_local_of_overlapCount_eq outside
    replacement_locallySmaller overlapCount_agrees

end Hypostructure.Fixtures.GraphBoundaryOverlap
