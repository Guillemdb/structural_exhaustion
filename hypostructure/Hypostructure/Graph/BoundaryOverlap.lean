import Hypostructure.Graph.BoundariedAtom

/-!
# Boundary-edge overlap under unrestricted gluing

Both sides of a boundary gluing may own the same boundary--boundary edge.
This module exposes that overlap as a graph on the labelled boundary and proves
the corresponding degree and edge-count inclusion--exclusion identities.

Local boundary-degree equality does not determine the overlap with an
unrestricted outside context.  Consequently, all replacement transfer
theorems below require the relevant overlap equality explicitly.
-/

namespace Hypostructure.Graph

universe u

namespace BoundaryPiece

/-- The graph induced by the edges that a piece owns between boundary labels. -/
def boundaryGraph {boundary : Boundary.{u}} (piece : BoundaryPiece boundary) :
    SimpleGraph boundary.Vertex :=
  piece.graph.comap Sum.inl

@[simp]
theorem boundaryGraph_adj {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (left right : boundary.Vertex) :
    piece.boundaryGraph.Adj left right ↔
      piece.graph.Adj (.inl left) (.inl right) :=
  Iff.rfl

end BoundaryPiece

namespace OutsideContext

/-- The graph induced by the edges that a context owns between boundary labels. -/
def boundaryGraph {boundary : Boundary.{u}}
    (outside : OutsideContext boundary) : SimpleGraph boundary.Vertex :=
  outside.graph.comap Sum.inl

@[simp]
theorem boundaryGraph_adj {boundary : Boundary.{u}}
    (outside : OutsideContext boundary) (left right : boundary.Vertex) :
    outside.boundaryGraph.Adj left right ↔
      outside.graph.Adj (.inl left) (.inl right) :=
  Iff.rfl

/-- Degree contributed by the context at one labelled boundary vertex. -/
def ownedBoundaryDegree {boundary : Boundary.{u}}
    (outside : OutsideContext boundary) (vertex : boundary.Vertex) : Nat :=
  outside.pack.degree (.inl vertex)

end OutsideContext

/-- Boundary edges owned simultaneously by a piece and an outside context. -/
def boundaryOverlapGraph {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph boundary.Vertex :=
  piece.boundaryGraph ⊓ outside.boundaryGraph

@[simp]
theorem boundaryOverlapGraph_adj_iff {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : boundary.Vertex) :
    (boundaryOverlapGraph piece outside).Adj left right ↔
      piece.graph.Adj (.inl left) (.inl right) ∧
        outside.graph.Adj (.inl left) (.inl right) := by
  simp [boundaryOverlapGraph]

/-- The overlap graph with its finite schedule and a decider inherited from
the two ownership predicates. -/
def boundaryOverlapObject {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    FiniteObject.{u} where
  Vertex := boundary.Vertex
  graph := boundaryOverlapGraph piece outside
  vertices := boundary.vertices
  decideAdj := fun left right => by
    letI : Decidable (piece.graph.Adj (.inl left) (.inl right)) :=
      piece.decideAdj _ _
    letI : Decidable (outside.graph.Adj (.inl left) (.inl right)) :=
      outside.decideAdj _ _
    exact decidable_of_iff
      (piece.graph.Adj (.inl left) (.inl right) ∧
        outside.graph.Adj (.inl left) (.inl right))
      (boundaryOverlapGraph_adj_iff piece outside left right).symm

/-- Number of common boundary-edge neighbours at one boundary label. -/
def boundaryOverlapDegree {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) : Nat :=
  (boundaryOverlapObject piece outside).degree vertex

/-- Complete pointwise overlap-degree profile against one outside context. -/
def boundaryOverlapDegreeProfile {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    boundary.Vertex → Nat :=
  fun vertex => boundaryOverlapDegree piece outside vertex

/-- Number of boundary edges owned by both sides of an unrestricted gluing. -/
def boundaryOverlapEdgeCount {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) : Nat :=
  (boundaryOverlapObject piece outside).edgeCount

theorem boundaryOverlapDegree_eq_ncard {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) :
    boundaryOverlapDegree piece outside vertex =
      ((boundaryOverlapGraph piece outside).neighborSet vertex).ncard := by
  exact FiniteObject.degree_eq_ncard_neighborSet
    (boundaryOverlapObject piece outside) vertex

theorem boundaryOverlapEdgeCount_eq_ncard {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    boundaryOverlapEdgeCount piece outside =
      (boundaryOverlapGraph piece outside).edgeSet.ncard := by
  exact FiniteObject.edgeCount_eq_ncard_edgeSet
    (boundaryOverlapObject piece outside)

/-- Piece-side contribution after embedding into the glued carrier. -/
def pieceContribution {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph (GluedVertex piece outside) :=
  piece.graph.map (pieceEmbedding piece outside)

/-- Context-side contribution after embedding into the glued carrier. -/
def contextContribution {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph (GluedVertex piece outside) :=
  outside.graph.map (contextEmbedding piece outside)

/-- Canonical inclusion of the common boundary into the glued carrier. -/
def boundaryEmbedding {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    boundary.Vertex ↪ GluedVertex piece outside where
  toFun := Sum.inl
  inj' := Sum.inl_injective

theorem glueGraph_eq_contribution_sup {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    glueGraph piece outside =
      pieceContribution piece outside ⊔ contextContribution piece outside :=
  rfl

theorem pieceEmbedding_eq_contextEmbedding_iff {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (pieceVertex : boundary.Vertex ⊕ piece.Internal)
    (contextVertex : boundary.Vertex ⊕ outside.Internal) :
    pieceEmbedding piece outside pieceVertex =
        contextEmbedding piece outside contextVertex ↔
      ∃ boundaryVertex, pieceVertex = .inl boundaryVertex ∧
        contextVertex = .inl boundaryVertex := by
  rcases pieceVertex with boundaryVertex | pieceInternal
  · rcases contextVertex with contextBoundary | outsideInternal
    · simp [pieceEmbedding, contextEmbedding, eq_comm]
    · simp [pieceEmbedding, contextEmbedding]
  · rcases contextVertex with contextBoundary | outsideInternal <;>
      simp [pieceEmbedding, contextEmbedding]

/-- The intersection of the two embedded contributions is exactly the common
boundary-edge graph embedded into the glued carrier. -/
theorem contribution_inf_eq_overlap_map {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    pieceContribution piece outside ⊓ contextContribution piece outside =
      (boundaryOverlapGraph piece outside).map
        (boundaryEmbedding piece outside) := by
  ext left right
  constructor
  · rintro ⟨pieceAdjacent, contextAdjacent⟩
    rcases (SimpleGraph.map_adj (pieceEmbedding piece outside)
      piece.graph left right).mp pieceAdjacent with
      ⟨pieceLeft, pieceRight, pieceEdge, pieceLeftEq, pieceRightEq⟩
    rcases (SimpleGraph.map_adj (contextEmbedding piece outside)
      outside.graph left right).mp contextAdjacent with
      ⟨contextLeft, contextRight, contextEdge, contextLeftEq, contextRightEq⟩
    have leftImages :
        pieceEmbedding piece outside pieceLeft =
          contextEmbedding piece outside contextLeft := by
      rw [pieceLeftEq, contextLeftEq]
    have rightImages :
        pieceEmbedding piece outside pieceRight =
          contextEmbedding piece outside contextRight := by
      rw [pieceRightEq, contextRightEq]
    rcases (pieceEmbedding_eq_contextEmbedding_iff piece outside
      pieceLeft contextLeft).mp leftImages with
      ⟨boundaryLeft, rfl, rfl⟩
    rcases (pieceEmbedding_eq_contextEmbedding_iff piece outside
      pieceRight contextRight).mp rightImages with
      ⟨boundaryRight, rfl, rfl⟩
    subst left
    subst right
    apply (SimpleGraph.map_adj_apply
      (G := boundaryOverlapGraph piece outside)
      (f := boundaryEmbedding piece outside)
      (a := boundaryLeft) (b := boundaryRight)).mpr
    exact (boundaryOverlapGraph_adj_iff piece outside
      boundaryLeft boundaryRight).mpr ⟨pieceEdge, contextEdge⟩
  · intro overlapAdjacent
    rcases (SimpleGraph.map_adj (boundaryEmbedding piece outside)
      (boundaryOverlapGraph piece outside) left right).mp overlapAdjacent with
      ⟨boundaryLeft, boundaryRight, overlapEdge, leftEq, rightEq⟩
    subst left
    subst right
    rw [boundaryOverlapGraph_adj_iff] at overlapEdge
    exact ⟨
      (SimpleGraph.map_adj_apply
        (G := piece.graph) (f := pieceEmbedding piece outside)
        (a := .inl boundaryLeft) (b := .inl boundaryRight)).mpr overlapEdge.1,
      (SimpleGraph.map_adj_apply
        (G := outside.graph) (f := contextEmbedding piece outside)
        (a := .inl boundaryLeft) (b := .inl boundaryRight)).mpr overlapEdge.2⟩

/-- Embedded piece degrees at boundary labels are the original local degrees. -/
theorem pieceContribution_boundaryDegree {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) :
    ((pieceContribution piece outside).neighborSet (.inl vertex)).ncard =
      piece.boundaryDegree vertex := by
  change ((pieceContribution piece outside).neighborSet
    (pieceEmbedding piece outside (.inl vertex))).ncard = _
  rw [pieceContribution, SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (pieceEmbedding piece outside).injective]
  rw [BoundaryPiece.boundaryDegree,
    FiniteObject.degree_eq_ncard_neighborSet]
  rfl

/-- Embedded context degrees at boundary labels are the original context degrees. -/
theorem contextContribution_boundaryDegree {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) :
    ((contextContribution piece outside).neighborSet (.inl vertex)).ncard =
      outside.ownedBoundaryDegree vertex := by
  change ((contextContribution piece outside).neighborSet
    (contextEmbedding piece outside (.inl vertex))).ncard = _
  rw [contextContribution, SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (contextEmbedding piece outside).injective]
  rw [OutsideContext.ownedBoundaryDegree,
    FiniteObject.degree_eq_ncard_neighborSet]
  rfl

/-- The intersection of the two embedded neighbour sets has exactly the
boundary-overlap degree. -/
theorem contribution_neighbor_inter_ncard {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) :
    ((pieceContribution piece outside).neighborSet (.inl vertex) ∩
      (contextContribution piece outside).neighborSet (.inl vertex)).ncard =
        boundaryOverlapDegree piece outside vertex := by
  rw [boundaryOverlapDegree_eq_ncard]
  have neighborInter :
      (pieceContribution piece outside).neighborSet (.inl vertex) ∩
          (contextContribution piece outside).neighborSet (.inl vertex) =
        (pieceContribution piece outside ⊓
          contextContribution piece outside).neighborSet (.inl vertex) := by
    ext neighbor
    simp
  rw [neighborInter, contribution_inf_eq_overlap_map]
  change (((boundaryOverlapGraph piece outside).map
    (boundaryEmbedding piece outside)).neighborSet
      (boundaryEmbedding piece outside vertex)).ncard = _
  rw [SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (boundaryEmbedding piece outside).injective]

/-- Exact boundary-degree inclusion--exclusion for unrestricted gluing. -/
theorem glue_boundaryDegree_add_overlap {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (vertex : boundary.Vertex) :
    (glue piece outside).degree (.inl vertex) +
        boundaryOverlapDegree piece outside vertex =
      piece.boundaryDegree vertex + outside.ownedBoundaryDegree vertex := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change ((glueGraph piece outside).neighborSet (.inl vertex)).ncard + _ = _
  have neighborUnion :
      (glueGraph piece outside).neighborSet (.inl vertex) =
        (pieceContribution piece outside).neighborSet (.inl vertex) ∪
          (contextContribution piece outside).neighborSet (.inl vertex) := by
    ext neighbor
    simp [glueGraph_eq_contribution_sup]
  rw [neighborUnion, ← contribution_neighbor_inter_ncard,
    Set.ncard_union_add_ncard_inter _ _ (Set.toFinite _) (Set.toFinite _),
    pieceContribution_boundaryDegree, contextContribution_boundaryDegree]

/-- Exact edge-count inclusion--exclusion for unrestricted gluing. -/
theorem glue_edgeCount_add_overlap {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (glue piece outside).edgeCount +
        boundaryOverlapEdgeCount piece outside =
      piece.edgeCount + outside.pack.edgeCount := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  rw [FiniteObject.edgeCount_eq_ncard_edgeSet]
  change (glueGraph piece outside).edgeSet.ncard + _ = _
  rw [glueGraph_eq_contribution_sup, SimpleGraph.edgeSet_sup]
  have pieceFinite :
      (pieceContribution piece outside).edgeSet.Finite := Set.toFinite _
  have contextFinite :
      (contextContribution piece outside).edgeSet.Finite := Set.toFinite _
  have overlapEdges :
      ((pieceContribution piece outside).edgeSet ∩
        (contextContribution piece outside).edgeSet).ncard =
          boundaryOverlapEdgeCount piece outside := by
    rw [boundaryOverlapEdgeCount_eq_ncard]
    rw [← SimpleGraph.edgeSet_inf,
      contribution_inf_eq_overlap_map, SimpleGraph.edgeSet_map,
      Set.ncard_image_of_injective _
        (boundaryEmbedding piece outside).sym2Map.injective]
  rw [← overlapEdges,
    Set.ncard_union_add_ncard_inter _ _ pieceFinite contextFinite]
  rw [pieceContribution, contextContribution,
    SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _
      (pieceEmbedding piece outside).sym2Map.injective,
    Set.ncard_image_of_injective _
      (contextEmbedding piece outside).sym2Map.injective]
  rw [BoundaryPiece.edgeCount, FiniteObject.edgeCount_eq_ncard_edgeSet,
    FiniteObject.edgeCount_eq_ncard_edgeSet]
  rfl

/-- Equality of local boundary degrees transfers to glued boundary degrees only
when the actual overlap-degree profiles against the context also agree. -/
theorem glue_boundaryDegree_eq_of_local_eq_of_overlap_eq
    {boundary : Boundary.{u}} {source replacement : BoundaryPiece boundary}
    (outside : OutsideContext boundary)
    (localDegrees : replacement.boundaryDegreeProfile =
      source.boundaryDegreeProfile)
    (overlapDegrees : boundaryOverlapDegreeProfile replacement outside =
      boundaryOverlapDegreeProfile source outside)
    (vertex : boundary.Vertex) :
    (glue replacement outside).degree (.inl vertex) =
      (glue source outside).degree (.inl vertex) := by
  have replacementCount := glue_boundaryDegree_add_overlap replacement outside vertex
  have sourceCount := glue_boundaryDegree_add_overlap source outside vertex
  have localAt := congrFun localDegrees vertex
  have overlapAt := congrFun overlapDegrees vertex
  dsimp [BoundaryPiece.boundaryDegreeProfile] at localAt
  dsimp [boundaryOverlapDegreeProfile] at overlapAt
  omega

/-- A local lexicographic decrease transfers through a fixed unrestricted
context when the total number of overlapped boundary edges is unchanged. -/
theorem glue_lexicographicallySmaller_of_local_of_overlapCount_eq
    {boundary : Boundary.{u}} {source replacement : BoundaryPiece boundary}
    (outside : OutsideContext boundary)
    (localSmaller : replacement.LocallySmaller source)
    (overlapCount : boundaryOverlapEdgeCount replacement outside =
      boundaryOverlapEdgeCount source outside) :
    (glue replacement outside).LexicographicallySmaller
      (glue source outside) := by
  rw [BoundaryPiece.locallySmaller_iff] at localSmaller
  rcases localSmaller with fewerVertices | ⟨sameVertices, fewerEdges⟩
  · apply FiniteObject.lexicographicallySmaller_of_vertexCount_lt
    simp only [glue_vertexCount]
    omega
  · apply FiniteObject.lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt
    · simp only [glue_vertexCount]
      omega
    · have replacementCount := glue_edgeCount_add_overlap replacement outside
      have sourceCount := glue_edgeCount_add_overlap source outside
      omega

end Hypostructure.Graph
