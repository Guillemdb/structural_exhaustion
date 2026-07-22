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

/-- A normalized outside context has no boundary-overlap graph with any
piece, because it owns no boundary--boundary edge. -/
theorem boundaryOverlapGraph_eq_bot_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges) :
    boundaryOverlapGraph piece outside = ⊥ := by
  ext left right
  rw [boundaryOverlapGraph_adj_iff]
  simp [noBoundaryEdges left right]

/-- A normalized outside context has zero boundary-overlap degree at every
label. -/
theorem boundaryOverlapDegree_eq_zero_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges)
    (vertex : boundary.Vertex) :
    boundaryOverlapDegree piece outside vertex = 0 := by
  rw [boundaryOverlapDegree_eq_ncard,
    boundaryOverlapGraph_eq_bot_of_context_noBoundaryEdges
      piece outside noBoundaryEdges]
  simp

/-- A normalized outside context has zero boundary-overlap edge count. -/
theorem boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges) :
    boundaryOverlapEdgeCount piece outside = 0 := by
  rw [boundaryOverlapEdgeCount_eq_ncard,
    boundaryOverlapGraph_eq_bot_of_context_noBoundaryEdges
      piece outside noBoundaryEdges]
  simp

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

/-- Embedded piece degrees at internal piece vertices are the original local
degrees. -/
theorem pieceContribution_internalDegree {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (internal : piece.Internal) :
    ((pieceContribution piece outside).neighborSet (.inr (.inl internal))).ncard =
      piece.pack.degree (.inr internal) := by
  change ((pieceContribution piece outside).neighborSet
    (pieceEmbedding piece outside (.inr internal))).ncard = _
  rw [pieceContribution, SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (pieceEmbedding piece outside).injective]
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  rfl

/-- Embedded context degrees at internal context vertices are the original
context degrees. -/
theorem contextContribution_internalDegree {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (internal : outside.Internal) :
    ((contextContribution piece outside).neighborSet (.inr (.inr internal))).ncard =
      outside.pack.degree (.inr internal) := by
  change ((contextContribution piece outside).neighborSet
    (contextEmbedding piece outside (.inr internal))).ncard = _
  rw [contextContribution, SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (contextEmbedding piece outside).injective]
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  rfl

/-- The context contribution has no neighbour at an internal piece vertex. -/
theorem contextContribution_pieceInternal_neighborSet_eq_empty
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) (internal : piece.Internal) :
    (contextContribution piece outside).neighborSet (.inr (.inl internal)) =
      ∅ := by
  ext neighbor
  constructor
  · intro adjacent
    rcases (SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph (.inr (.inl internal)) neighbor).mp adjacent with
      ⟨contextLeft, _contextRight, _edge, leftEq, _rightEq⟩
    cases contextLeft <;> simp [contextEmbedding] at leftEq
  · simp

/-- The piece contribution has no neighbour at an internal context vertex. -/
theorem pieceContribution_contextInternal_neighborSet_eq_empty
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) (internal : outside.Internal) :
    (pieceContribution piece outside).neighborSet (.inr (.inr internal)) =
      ∅ := by
  ext neighbor
  constructor
  · intro adjacent
    rcases (SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph (.inr (.inr internal)) neighbor).mp adjacent with
      ⟨pieceLeft, _pieceRight, _edge, leftEq, _rightEq⟩
    cases pieceLeft <;> simp [pieceEmbedding] at leftEq
  · simp

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

/-- Under normalized context ownership, local boundary-degree equality
transfers directly to final glued boundary-degree equality. -/
theorem glue_boundaryDegree_eq_of_local_eq_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} {source replacement : BoundaryPiece boundary}
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges)
    (localDegrees : replacement.boundaryDegreeProfile =
      source.boundaryDegreeProfile)
    (vertex : boundary.Vertex) :
    (glue replacement outside).degree (.inl vertex) =
      (glue source outside).degree (.inl vertex) := by
  apply glue_boundaryDegree_eq_of_local_eq_of_overlap_eq outside localDegrees
  funext vertex
  change boundaryOverlapDegree replacement outside vertex =
    boundaryOverlapDegree source outside vertex
  rw [boundaryOverlapDegree_eq_zero_of_context_noBoundaryEdges
    replacement outside noBoundaryEdges vertex,
    boundaryOverlapDegree_eq_zero_of_context_noBoundaryEdges
    source outside noBoundaryEdges vertex]

/-- Exact edge-count additivity for normalized outside contexts. -/
theorem glue_edgeCount_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges) :
    (glue piece outside).edgeCount =
      piece.edgeCount + outside.pack.edgeCount := by
  have count := glue_edgeCount_add_overlap piece outside
  rw [boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
    piece outside noBoundaryEdges] at count
  simpa using count

/-- Internal atom degrees are unchanged by unrestricted gluing. -/
theorem glue_degree_pieceInternal {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (internal : piece.Internal) :
    (glue piece outside).degree (.inr (.inl internal)) =
      piece.pack.degree (.inr internal) := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change ((glueGraph piece outside).neighborSet
    (.inr (.inl internal))).ncard = _
  have neighborUnion :
      (glueGraph piece outside).neighborSet (.inr (.inl internal)) =
        (pieceContribution piece outside).neighborSet (.inr (.inl internal)) ∪
          (contextContribution piece outside).neighborSet
            (.inr (.inl internal)) := by
    ext neighbor
    simp [glueGraph_eq_contribution_sup]
  rw [neighborUnion,
    contextContribution_pieceInternal_neighborSet_eq_empty]
  simpa using pieceContribution_internalDegree piece outside internal

/-- Internal context degrees are unchanged by unrestricted gluing. -/
theorem glue_degree_contextInternal {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (internal : outside.Internal) :
    (glue piece outside).degree (.inr (.inr internal)) =
      outside.pack.degree (.inr internal) := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change ((glueGraph piece outside).neighborSet
    (.inr (.inr internal))).ncard = _
  have neighborUnion :
      (glueGraph piece outside).neighborSet (.inr (.inr internal)) =
        (pieceContribution piece outside).neighborSet (.inr (.inr internal)) ∪
          (contextContribution piece outside).neighborSet
            (.inr (.inr internal)) := by
    ext neighbor
    simp [glueGraph_eq_contribution_sup]
  rw [neighborUnion,
    pieceContribution_contextInternal_neighborSet_eq_empty]
  simpa using contextContribution_internalDegree piece outside internal

/-- Equal local boundary degrees and an internal threshold certificate
preserve a minimum-degree lower bound under normalized gluing. -/
theorem glue_minDegree_ge_of_local_boundary_eq_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} (threshold : Nat)
    {source replacement : BoundaryPiece boundary}
    (outside : OutsideContext boundary)
    (boundaryNonempty : Nonempty boundary.Vertex)
    (noBoundaryEdges : outside.NoBoundaryEdges)
    (localDegrees : replacement.boundaryDegreeProfile =
      source.boundaryDegreeProfile)
    (replacementInternal :
      replacement.InternalThresholdBaseline threshold)
    (sourceBaseline : threshold ≤ (glue source outside).minDegree) :
    threshold ≤ (glue replacement outside).minDegree := by
  letI : Nonempty (glue replacement outside).Vertex := by
    rcases boundaryNonempty with ⟨vertex⟩
    exact ⟨.inl vertex⟩
  apply (glue replacement outside).le_minDegree_of_forall_le_degree
  intro vertex
  cases vertex with
  | inl boundaryVertex =>
      have sourceDegree : threshold ≤
          (glue source outside).degree (.inl boundaryVertex) :=
        sourceBaseline.trans
          ((glue source outside).minDegree_le_degree (.inl boundaryVertex))
      rw [glue_boundaryDegree_eq_of_local_eq_of_context_noBoundaryEdges
        outside noBoundaryEdges localDegrees boundaryVertex]
      exact sourceDegree
  | inr internal =>
      cases internal with
      | inl replacementInternalVertex =>
          rw [glue_degree_pieceInternal replacement outside
            replacementInternalVertex]
          exact replacementInternal replacementInternalVertex
      | inr outsideInternalVertex =>
          have sourceDegree : threshold ≤
              (glue source outside).degree
                (.inr (.inr outsideInternalVertex)) :=
            sourceBaseline.trans
              ((glue source outside).minDegree_le_degree
                (.inr (.inr outsideInternalVertex)))
          rw [glue_degree_contextInternal source outside
              outsideInternalVertex] at sourceDegree
          rw [glue_degree_contextInternal replacement outside
              outsideInternalVertex]
          exact sourceDegree

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

/-- A local lexicographic decrease transfers through a normalized outside
context without an explicit overlap-count hypothesis. -/
theorem glue_lexicographicallySmaller_of_local_of_context_noBoundaryEdges
    {boundary : Boundary.{u}} {source replacement : BoundaryPiece boundary}
    (outside : OutsideContext boundary)
    (noBoundaryEdges : outside.NoBoundaryEdges)
    (localSmaller : replacement.LocallySmaller source) :
    (glue replacement outside).LexicographicallySmaller
      (glue source outside) := by
  apply glue_lexicographicallySmaller_of_local_of_overlapCount_eq outside
    localSmaller
  rw [boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
      replacement outside noBoundaryEdges,
    boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
      source outside noBoundaryEdges]

end Hypostructure.Graph
