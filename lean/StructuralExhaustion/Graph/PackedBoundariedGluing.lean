import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import StructuralExhaustion.CT3.CertifiedCompression
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Graph.PackedBoundariedGluing

open StructuralExhaustion

universe u

/-!
# Literal finite boundaried-graph gluing

Boundary vertices are represented by the left summand and internal vertices by
the right summand.  Outside contexts are normalized to own no
boundary--boundary edge; those edges belong to the atom side.  Consequently the two mapped
edge sets in `glue` are disjoint, so both vertex and edge changes of a piece
lift exactly to the glued graph.  This is the concrete graph theorem needed by
minimal-counterexample replacement arguments.
-/

/-- A finite graph with a distinguished, labelled boundary. -/
structure BoundariedGraph (T : Type u) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (T ⊕ Internal)
  decideAdj : DecidableRel graph.Adj

/-- An atom-side piece.  It owns the boundary--boundary edges of the chosen
decomposition, so a replacement may change those edges. -/
abbrev Piece (T : Type u) := BoundariedGraph T

/-- A normalized outside context.  Boundary--boundary edges are owned by the
atom side, so the two edge sets are literally disjoint after gluing. -/
structure Context (T : Type u) extends BoundariedGraph T where
  noBoundaryEdge : ∀ left right : T,
    ¬ graph.Adj (.inl left) (.inl right)

namespace BoundariedGraph

variable {T : Type u}

/-- Number of internal vertices; the common boundary is deliberately not
counted in the local replacement order. -/
def internalVertexCount (piece : BoundariedGraph T) : Nat :=
  letI : FinEnum piece.Internal := piece.internalVertices
  Fintype.card piece.Internal

/-- Number of locally owned edges. -/
def edgeCount [FinEnum T] (piece : BoundariedGraph T) : Nat := by
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  exact piece.graph.edgeFinset.card

end BoundariedGraph

namespace Piece

variable {T : Type u}

def internalVertexCount (piece : Piece T) : Nat :=
  letI : FinEnum piece.Internal := piece.internalVertices
  Fintype.card piece.Internal

def edgeCount [FinEnum T] (piece : Piece T) : Nat := by
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  exact piece.graph.edgeFinset.card

/-- The manuscript's lexicographic local order, with the fixed boundary
removed from the vertex coordinate. -/
def LexSmaller [FinEnum T] (replacement source : Piece T) : Prop :=
  replacement.internalVertexCount < source.internalVertexCount ∨
    (replacement.internalVertexCount = source.internalVertexCount ∧
      replacement.edgeCount < source.edgeCount)

/-- Local degree at a labelled boundary vertex. -/
def boundaryDegree (boundaries : FinEnum T) (piece : Piece T)
    (boundary : T) : Nat := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  exact piece.graph.degree (.inl boundary)

/-- Minimum-degree requirement on the vertices internal to a replacement
piece. -/
def InternalBaseline (boundaries : FinEnum T) (threshold : Nat)
    (piece : Piece T) : Prop :=
  ∀ internal : piece.Internal,
    threshold ≤
      (letI : FinEnum T := boundaries
       letI : FinEnum piece.Internal := piece.internalVertices
       letI : DecidableRel piece.graph.Adj := piece.decideAdj
       piece.graph.degree (.inr internal))

/-- A piece regarded as an ordinary packed finite graph. -/
def pack (boundaries : FinEnum T) (piece : Piece T) : PackedFiniteObject where
  Vertex := T ⊕ piece.Internal
  object := {
    graph := piece.graph
    input := {
      vertices := by
        letI : FinEnum T := boundaries
        letI : FinEnum piece.Internal := piece.internalVertices
        infer_instance
      decideAdj := piece.decideAdj
    }
  }

end Piece

namespace Context

variable {T : Type u}

def internalVertexCount (outside : Context T) : Nat :=
  letI : FinEnum outside.Internal := outside.internalVertices
  Fintype.card outside.Internal

def edgeCount [FinEnum T] (outside : Context T) : Nat := by
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  exact outside.graph.edgeFinset.card

end Context

section Glue

variable {T : Type u} (boundaries : FinEnum T)

private theorem edgeFinset_card_eq_ncard {V : Type u} [Fintype V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] :
    graph.edgeFinset.card = graph.edgeSet.ncard := by
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rfl

private def pieceEmbedding (piece : Piece T) (outside : Context T) :
    (T ⊕ piece.Internal) ↪ (T ⊕ (piece.Internal ⊕ outside.Internal)) where
  toFun
    | .inl boundary => .inl boundary
    | .inr internal => .inr (.inl internal)
  inj' := by
    intro left right equality
    cases left <;> cases right <;> simp_all

private def contextEmbedding (piece : Piece T) (outside : Context T) :
    (T ⊕ outside.Internal) ↪ (T ⊕ (piece.Internal ⊕ outside.Internal)) where
  toFun
    | .inl boundary => .inl boundary
    | .inr internal => .inr (.inr internal)
  inj' := by
    intro left right equality
    cases left <;> cases right <;> simp_all

/-- Literal gluing: identify equal boundary labels and take the union of the
two edge sets. -/
def glueGraph (piece : Piece T) (outside : Context T) :
    SimpleGraph (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
  piece.graph.map (pieceEmbedding piece outside) ⊔
    outside.graph.map (contextEmbedding piece outside)

/-- The glued graph with its deterministic finite input. -/
noncomputable def glue (piece : Piece T) (outside : Context T) : PackedFiniteObject where
  Vertex := T ⊕ (piece.Internal ⊕ outside.Internal)
  object := {
    graph := glueGraph piece outside
    input := {
      vertices := by
        letI : FinEnum T := boundaries
        letI : FinEnum piece.Internal := piece.internalVertices
        letI : FinEnum outside.Internal := outside.internalVertices
        infer_instance
      decideAdj := Classical.decRel _
    }
  }

@[simp] theorem glue_vertexCount (piece : Piece T) (outside : Context T) :
    (glue boundaries piece outside).vertexCount =
      Fintype.card T + piece.internalVertexCount +
        outside.internalVertexCount := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  simp [glue, PackedFiniteObject.vertexCount, FinEnum.card_eq_fintypeCard,
    Piece.internalVertexCount, Context.internalVertexCount,
    Nat.add_assoc]

private theorem mappedGraphs_disjoint (piece : Piece T) (outside : Context T) :
    Disjoint
      (piece.graph.map (pieceEmbedding piece outside))
      (outside.graph.map (contextEmbedding piece outside)) := by
  rw [SimpleGraph.disjoint_left]
  intro left right pieceAdjacent outsideAdjacent
  rcases (SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph
      left right).1 pieceAdjacent with
    ⟨pieceLeft, pieceRight, pieceEdge, leftEq, rightEq⟩
  rcases (SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph
      left right).1 outsideAdjacent with
    ⟨outsideLeft, outsideRight, outsideEdge, leftEq', rightEq'⟩
  have leftImages : pieceEmbedding piece outside pieceLeft =
      contextEmbedding piece outside outsideLeft := leftEq.trans leftEq'.symm
  have rightImages : pieceEmbedding piece outside pieceRight =
      contextEmbedding piece outside outsideRight := rightEq.trans rightEq'.symm
  have pieceLeftBoundary : ∃ boundary, pieceLeft = Sum.inl boundary := by
    cases pieceLeft with
    | inl boundary => exact ⟨boundary, rfl⟩
    | inr internal =>
        cases outsideLeft <;> simp [pieceEmbedding, contextEmbedding] at leftImages
  have pieceRightBoundary : ∃ boundary, pieceRight = Sum.inl boundary := by
    cases pieceRight with
    | inl boundary => exact ⟨boundary, rfl⟩
    | inr internal =>
        cases outsideRight <;> simp [pieceEmbedding, contextEmbedding] at rightImages
  rcases pieceLeftBoundary with ⟨pieceLeftBoundary, rfl⟩
  rcases pieceRightBoundary with ⟨pieceRightBoundary, rfl⟩
  cases outsideLeft with
  | inl outsideLeftBoundary =>
      cases outsideRight with
      | inl outsideRightBoundary =>
          exact outside.noBoundaryEdge outsideLeftBoundary
            outsideRightBoundary outsideEdge
      | inr outsideInternal =>
          simp [pieceEmbedding, contextEmbedding] at rightImages
  | inr outsideInternal =>
      simp [pieceEmbedding, contextEmbedding] at leftImages

/-- Exact edge-count additivity of normalized gluing. -/
theorem glue_edgeCount (piece : Piece T) (outside : Context T) :
    (glue boundaries piece outside).edgeCount =
      piece.edgeCount + outside.edgeCount := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  have packedEdgeCount : (glue boundaries piece outside).edgeCount =
      (glueGraph piece outside).edgeSet.ncard := by
    let packed := glue boundaries piece outside
    letI : FinEnum packed.Vertex := packed.object.input.vertices
    letI : DecidableRel packed.object.graph.Adj := packed.object.input.decideAdj
    change packed.object.edgeCount = packed.object.graph.edgeSet.ncard
    unfold FiniteObject.edgeCount
    exact edgeFinset_card_eq_ncard packed.object.graph
  have pieceEdgeCount : piece.edgeCount = piece.graph.edgeSet.ncard := by
    unfold Piece.edgeCount
    exact edgeFinset_card_eq_ncard piece.graph
  have outsideEdgeCount : outside.edgeCount = outside.graph.edgeSet.ncard := by
    unfold Context.edgeCount
    exact edgeFinset_card_eq_ncard outside.graph
  rw [packedEdgeCount, pieceEdgeCount, outsideEdgeCount]
  rw [glueGraph, SimpleGraph.edgeSet_sup]
  rw [Set.ncard_union_eq
    (SimpleGraph.disjoint_edgeSet.mpr (mappedGraphs_disjoint piece outside))]
  rw [SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map]
  rw [Set.ncard_image_of_injective _ (pieceEmbedding piece outside).sym2Map.injective]
  rw [Set.ncard_image_of_injective _
    (contextEmbedding piece outside).sym2Map.injective]

/-- A strict local lexicographic decrease gives a strict decrease of the
whole glued packed graph.  No whole-graph decrease is assumed. -/
theorem glue_lexRank_lt {replacement source : Piece T} (outside : Context T)
    (smaller : Piece.LexSmaller replacement source) :
    (glue boundaries replacement outside).lexRank <
      (glue boundaries source outside).lexRank := by
  rcases smaller with vertexLt | ⟨vertexEq, edgeLt⟩
  · apply PackedFiniteObject.lexRank_lt_of_vertexCount_lt
    simp only [glue_vertexCount, Piece.internalVertexCount] at vertexLt ⊢
    omega
  · apply PackedFiniteObject.lexRank_lt_of_vertexCount_eq_edgeCount_lt
    · simp only [glue_vertexCount, Piece.internalVertexCount] at vertexEq ⊢
      omega
    · rw [glue_edgeCount, glue_edgeCount]
      exact Nat.add_lt_add_right edgeLt _

private theorem glue_neighborSet_pieceInternal (piece : Piece T)
    (outside : Context T) (internal : piece.Internal) :
    (glueGraph piece outside).neighborSet (.inr (.inl internal)) =
      pieceEmbedding piece outside ''
        piece.graph.neighborSet (.inr internal) := by
  ext vertex
  constructor
  · intro adjacent
    change (glueGraph piece outside).Adj (.inr (.inl internal)) vertex at adjacent
    rcases adjacent with pieceAdjacent | outsideAdjacent
    · rcases (SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph
          _ _).1 pieceAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left with
      | inl boundary => simp [pieceEmbedding] at leftEq
      | inr sourceInternal =>
          simp [pieceEmbedding] at leftEq
          subst sourceInternal
          exact ⟨right, edge, rightEq⟩
    · rcases (SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph
          _ _).1 outsideAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left <;> simp [contextEmbedding] at leftEq
  · rintro ⟨vertex, adjacent, rfl⟩
    exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph
      _ _).2 ⟨_, _, adjacent, rfl, rfl⟩)

private theorem glue_neighborSet_contextInternal (piece : Piece T)
    (outside : Context T) (internal : outside.Internal) :
    (glueGraph piece outside).neighborSet (.inr (.inr internal)) =
      contextEmbedding piece outside ''
        outside.graph.neighborSet (.inr internal) := by
  ext vertex
  constructor
  · intro adjacent
    change (glueGraph piece outside).Adj (.inr (.inr internal)) vertex at adjacent
    rcases adjacent with pieceAdjacent | outsideAdjacent
    · rcases (SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph
          _ _).1 pieceAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left <;> simp [pieceEmbedding] at leftEq
    · rcases (SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph
          _ _).1 outsideAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left with
      | inl boundary => simp [contextEmbedding] at leftEq
      | inr outsideInternal =>
          simp [contextEmbedding] at leftEq
          subst outsideInternal
          exact ⟨right, edge, rightEq⟩
  · rintro ⟨vertex, adjacent, rfl⟩
    exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph
      _ _).2 ⟨_, _, adjacent, rfl, rfl⟩)

private theorem glue_neighborSet_boundary (piece : Piece T)
    (outside : Context T) (boundary : T) :
    (glueGraph piece outside).neighborSet (.inl boundary) =
      pieceEmbedding piece outside ''
          piece.graph.neighborSet (.inl boundary) ∪
        contextEmbedding piece outside ''
          outside.graph.neighborSet (.inl boundary) := by
  ext vertex
  constructor
  · intro adjacent
    change (glueGraph piece outside).Adj (.inl boundary) vertex at adjacent
    rcases adjacent with pieceAdjacent | outsideAdjacent
    · left
      rcases (SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph
          _ _).1 pieceAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left with
      | inl sourceBoundary =>
          simp [pieceEmbedding] at leftEq
          subst sourceBoundary
          exact ⟨right, edge, rightEq⟩
      | inr internal => simp [pieceEmbedding] at leftEq
    · right
      rcases (SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph
          _ _).1 outsideAdjacent with ⟨left, right, edge, leftEq, rightEq⟩
      cases left with
      | inl contextBoundary =>
          simp [contextEmbedding] at leftEq
          subst contextBoundary
          exact ⟨right, edge, rightEq⟩
      | inr internal => simp [contextEmbedding] at leftEq
  · rintro (pieceNeighbor | outsideNeighbor)
    · rcases pieceNeighbor with ⟨vertex, adjacent, rfl⟩
      exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph _ _).2 ⟨_, _, adjacent, rfl, rfl⟩)
    · rcases outsideNeighbor with ⟨vertex, adjacent, rfl⟩
      exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph _ _).2 ⟨_, _, adjacent, rfl, rfl⟩)

private theorem boundary_neighbor_images_disjoint (piece : Piece T)
    (outside : Context T) (boundary : T) :
    Disjoint
      (pieceEmbedding piece outside '' piece.graph.neighborSet (.inl boundary))
      (contextEmbedding piece outside ''
        outside.graph.neighborSet (.inl boundary)) := by
  rw [Set.disjoint_left]
  intro vertex pieceMember outsideMember
  rcases pieceMember with ⟨pieceNeighbor, pieceEdge, pieceEq⟩
  rcases outsideMember with ⟨outsideNeighbor, outsideEdge, outsideEq⟩
  have pieceMapped :
      (piece.graph.map (pieceEmbedding piece outside)).Adj (.inl boundary) vertex :=
    (SimpleGraph.map_adj (pieceEmbedding piece outside) piece.graph _ _).2
      ⟨_, _, pieceEdge, rfl, pieceEq⟩
  have outsideMapped :
      (outside.graph.map (contextEmbedding piece outside)).Adj
        (.inl boundary) vertex :=
    (SimpleGraph.map_adj (contextEmbedding piece outside) outside.graph _ _).2
      ⟨_, _, outsideEdge, rfl, outsideEq⟩
  exact (SimpleGraph.disjoint_left.mp (mappedGraphs_disjoint piece outside)
    _ _ pieceMapped) outsideMapped

private theorem degree_eq_ncard_neighborSet {V : Type u} [Fintype V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] (vertex : V) :
    graph.degree vertex = (graph.neighborSet vertex).ncard := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]

/-- Internal atom degrees are unchanged by literal gluing. -/
theorem glue_degree_pieceInternal (piece : Piece T) (outside : Context T)
    (internal : piece.Internal) :
    (letI : FinEnum T := boundaries
     letI : FinEnum piece.Internal := piece.internalVertices
     letI : FinEnum outside.Internal := outside.internalVertices
     letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
     letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
       @FinEnum.instFintype _ inferInstance
     letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
     (glueGraph piece outside).degree (.inr (.inl internal))) =
      (letI : FinEnum T := boundaries
       letI : FinEnum piece.Internal := piece.internalVertices
       letI : DecidableRel piece.graph.Adj := piece.decideAdj
       piece.graph.degree (.inr internal)) := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
  letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
    @FinEnum.instFintype _ inferInstance
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
  rw [degree_eq_ncard_neighborSet, degree_eq_ncard_neighborSet,
    glue_neighborSet_pieceInternal]
  exact Set.ncard_image_of_injective _ (pieceEmbedding piece outside).injective

/-- Internal context degrees are unchanged by literal gluing. -/
theorem glue_degree_contextInternal (piece : Piece T) (outside : Context T)
    (internal : outside.Internal) :
    (letI : FinEnum T := boundaries
     letI : FinEnum piece.Internal := piece.internalVertices
     letI : FinEnum outside.Internal := outside.internalVertices
     letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
     letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
       @FinEnum.instFintype _ inferInstance
     letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
     (glueGraph piece outside).degree (.inr (.inr internal))) =
      (letI : FinEnum T := boundaries
       letI : FinEnum outside.Internal := outside.internalVertices
       letI : DecidableRel outside.graph.Adj := outside.decideAdj
       outside.graph.degree (.inr internal)) := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
  letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
    @FinEnum.instFintype _ inferInstance
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
  rw [degree_eq_ncard_neighborSet, degree_eq_ncard_neighborSet,
    glue_neighborSet_contextInternal]
  exact Set.ncard_image_of_injective _ (contextEmbedding piece outside).injective

/-- Boundary degrees add exactly because outside contexts own no
boundary--boundary edge. -/
theorem glue_degree_boundary (piece : Piece T) (outside : Context T)
    (boundary : T) :
    (letI : FinEnum T := boundaries
     letI : FinEnum piece.Internal := piece.internalVertices
     letI : FinEnum outside.Internal := outside.internalVertices
     letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
     letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
       @FinEnum.instFintype _ inferInstance
     letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
     (glueGraph piece outside).degree (.inl boundary)) =
      (letI : FinEnum T := boundaries
       letI : FinEnum piece.Internal := piece.internalVertices
       letI : DecidableRel piece.graph.Adj := piece.decideAdj
       piece.graph.degree (.inl boundary)) +
      (letI : FinEnum T := boundaries
       letI : FinEnum outside.Internal := outside.internalVertices
       letI : DecidableRel outside.graph.Adj := outside.decideAdj
       outside.graph.degree (.inl boundary)) := by
  letI : FinEnum T := boundaries
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : FinEnum (T ⊕ (piece.Internal ⊕ outside.Internal)) := inferInstance
  letI : Fintype (T ⊕ (piece.Internal ⊕ outside.Internal)) :=
    @FinEnum.instFintype _ inferInstance
  letI : DecidableRel piece.graph.Adj := piece.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  letI : DecidableRel (glueGraph piece outside).Adj := Classical.decRel _
  rw [degree_eq_ncard_neighborSet, degree_eq_ncard_neighborSet,
    degree_eq_ncard_neighborSet, glue_neighborSet_boundary]
  rw [Set.ncard_union_eq
    (boundary_neighbor_images_disjoint piece outside boundary)]
  rw [Set.ncard_image_of_injective _ (pieceEmbedding piece outside).injective]
  rw [Set.ncard_image_of_injective _
    (contextEmbedding piece outside).injective]

/-- Equal local boundary degrees and an internal minimum-degree certificate
preserve the global minimum-degree baseline under literal gluing. -/
theorem glue_preserves_minDegree [Nonempty T] (threshold : Nat)
    (source replacement : Piece T) (outside : Context T)
    (boundaryDegreeEq : ∀ boundary,
      replacement.boundaryDegree boundaries boundary =
        source.boundaryDegree boundaries boundary)
    (replacementInternal : replacement.InternalBaseline boundaries threshold)
    (sourceBaseline : threshold ≤
      (letI : FinEnum T := boundaries
       letI : FinEnum source.Internal := source.internalVertices
       letI : FinEnum outside.Internal := outside.internalVertices
       letI : FinEnum (T ⊕ (source.Internal ⊕ outside.Internal)) := inferInstance
       letI : Fintype (T ⊕ (source.Internal ⊕ outside.Internal)) :=
         @FinEnum.instFintype _ inferInstance
       letI : DecidableRel (glueGraph source outside).Adj := Classical.decRel _
       (glueGraph source outside).minDegree)) :
    threshold ≤
      (letI : FinEnum T := boundaries
       letI : FinEnum replacement.Internal := replacement.internalVertices
       letI : FinEnum outside.Internal := outside.internalVertices
       letI : FinEnum (T ⊕ (replacement.Internal ⊕ outside.Internal)) :=
         inferInstance
       letI : Fintype (T ⊕ (replacement.Internal ⊕ outside.Internal)) :=
         @FinEnum.instFintype _ inferInstance
       letI : DecidableRel (glueGraph replacement outside).Adj := Classical.decRel _
       (glueGraph replacement outside).minDegree) := by
  letI : FinEnum T := boundaries
  letI : FinEnum source.Internal := source.internalVertices
  letI : FinEnum replacement.Internal := replacement.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : FinEnum (T ⊕ (source.Internal ⊕ outside.Internal)) := inferInstance
  letI : FinEnum (T ⊕ (replacement.Internal ⊕ outside.Internal)) := inferInstance
  letI : Fintype (T ⊕ (source.Internal ⊕ outside.Internal)) :=
    @FinEnum.instFintype _ inferInstance
  letI : Fintype (T ⊕ (replacement.Internal ⊕ outside.Internal)) :=
    @FinEnum.instFintype _ inferInstance
  letI : DecidableRel source.graph.Adj := source.decideAdj
  letI : DecidableRel replacement.graph.Adj := replacement.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  letI : DecidableRel (glueGraph source outside).Adj := Classical.decRel _
  letI : DecidableRel (glueGraph replacement outside).Adj := Classical.decRel _
  apply (glueGraph replacement outside).le_minDegree_of_forall_le_degree threshold
  intro vertex
  cases vertex with
  | inl boundary =>
      have sourceDegree := sourceBaseline.trans
        ((glueGraph source outside).minDegree_le_degree (.inl boundary))
      rw [glue_degree_boundary boundaries source outside boundary] at sourceDegree
      rw [glue_degree_boundary boundaries replacement outside boundary]
      have degreeEq := boundaryDegreeEq boundary
      simp only [Piece.boundaryDegree] at degreeEq
      rw [degreeEq]
      exact sourceDegree
  | inr internal =>
      cases internal with
      | inl replacementInternalVertex =>
          rw [glue_degree_pieceInternal boundaries replacement outside]
          exact replacementInternal replacementInternalVertex
      | inr outsideInternalVertex =>
          have sourceDegree := sourceBaseline.trans
            ((glueGraph source outside).minDegree_le_degree
              (.inr (.inr outsideInternalVertex)))
          rw [glue_degree_contextInternal boundaries source outside] at sourceDegree
          rw [glue_degree_contextInternal boundaries replacement outside]
          exact sourceDegree

/-! ## Transport across a concrete reconstruction isomorphism -/

private theorem iso_degree_eq {V W : Type u} [Fintype V] [Fintype W]
    {left : SimpleGraph V} {right : SimpleGraph W}
    [DecidableRel left.Adj] [DecidableRel right.Adj]
    (iso : left ≃g right) (vertex : V) :
    left.degree vertex = right.degree (iso vertex) := by
  apply Nat.le_antisymm
  · exact iso.toCopy.degree_le vertex
  · convert iso.symm.toCopy.degree_le (iso vertex) using 1
    simp

private theorem minDegree_mono_of_iso {left right : PackedFiniteObject.{u}}
    (iso : left.object.graph ≃g right.object.graph) (threshold : Nat)
    (leftBaseline : threshold ≤ left.object.minDegree) :
    threshold ≤ right.object.minDegree := by
  letI : FinEnum left.Vertex := left.object.input.vertices
  letI : FinEnum right.Vertex := right.object.input.vertices
  letI : DecidableRel left.object.graph.Adj := left.object.input.decideAdj
  letI : DecidableRel right.object.graph.Adj := right.object.input.decideAdj
  change threshold ≤ left.object.graph.minDegree at leftBaseline
  change threshold ≤ right.object.graph.minDegree
  cases isEmpty_or_nonempty right.Vertex with
  | inl empty =>
      letI : IsEmpty right.Vertex := empty
      have leftEmpty : IsEmpty left.Vertex :=
        ⟨fun vertex => isEmptyElim (iso vertex)⟩
      letI : IsEmpty left.Vertex := leftEmpty
      rw [left.object.graph.minDegree_of_isEmpty] at leftBaseline
      rw [right.object.graph.minDegree_of_isEmpty]
      exact leftBaseline
  | inr nonempty =>
      letI : Nonempty right.Vertex := nonempty
      apply right.object.graph.le_minDegree_of_forall_le_degree threshold
      intro vertex
      have leftDegree := leftBaseline.trans
        (left.object.graph.minDegree_le_degree (iso.symm vertex))
      rw [iso_degree_eq iso (iso.symm vertex)] at leftDegree
      simpa using leftDegree

/-- A graph isomorphism transports the minimum-degree baseline in both
directions. -/
theorem minDegree_iff_of_iso {left right : PackedFiniteObject.{u}}
    (iso : left.object.graph ≃g right.object.graph) (threshold : Nat) :
    threshold ≤ left.object.minDegree ↔
      threshold ≤ right.object.minDegree :=
  ⟨minDegree_mono_of_iso iso threshold,
    minDegree_mono_of_iso iso.symm threshold⟩

/-- Packed lexicographic rank is invariant under graph isomorphism. -/
theorem lexRank_eq_of_iso {left right : PackedFiniteObject.{u}}
    (iso : left.object.graph ≃g right.object.graph) :
    left.lexRank = right.lexRank := by
  letI : FinEnum left.Vertex := left.object.input.vertices
  letI : FinEnum right.Vertex := right.object.input.vertices
  letI : DecidableRel left.object.graph.Adj := left.object.input.decideAdj
  letI : DecidableRel right.object.graph.Adj := right.object.input.decideAdj
  have vertexEq : left.vertexCount = right.vertexCount := by
    simp only [PackedFiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]
    exact Fintype.card_congr iso.toEquiv
  have edgeEq : left.edgeCount = right.edgeCount := by
    unfold PackedFiniteObject.edgeCount FiniteObject.edgeCount
    exact iso.card_edgeFinset_eq
  simp [PackedFiniteObject.lexRank, vertexEq, edgeEq]

/-- Cycle targets with an arbitrary length predicate are invariant under graph
isomorphism. -/
theorem hasCycleWithLength_iff_of_iso {left right : PackedFiniteObject.{u}}
    (iso : left.object.graph ≃g right.object.graph) (LengthOK : Nat → Prop) :
    HasCycleWithLength left.object.graph LengthOK ↔
      HasCycleWithLength right.object.graph LengthOK := by
  constructor
  · exact hasCycleWithLength_mapHom iso.toHom iso.toEquiv.injective
  · exact hasCycleWithLength_mapHom iso.symm.toHom iso.symm.toEquiv.injective

end Glue

namespace MinimumDegreeCycleReplacement

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable {T : Type u} (boundaries : FinEnum T) [Nonempty T]

theorem glue_preserves_problemBaseline (source replacement : Piece T)
    (outside : Context T)
    (profileEq : ∀ boundary,
      replacement.boundaryDegree boundaries boundary =
        source.boundaryDegree boundaries boundary)
    (internal : replacement.InternalBaseline boundaries input.minimumDegree)
    (sourceBaseline : input.problem.Baseline
      (glue boundaries source outside)) :
    input.problem.Baseline (glue boundaries replacement outside) := by
  have sourceBaseline' : input.minimumDegree ≤
      (letI : FinEnum T := boundaries
       letI : FinEnum source.Internal := source.internalVertices
       letI : FinEnum outside.Internal := outside.internalVertices
       letI : FinEnum (T ⊕ (source.Internal ⊕ outside.Internal)) := inferInstance
       letI : Fintype (T ⊕ (source.Internal ⊕ outside.Internal)) :=
         @FinEnum.instFintype _ inferInstance
       letI : DecidableRel (glueGraph source outside).Adj := Classical.decRel _
       (glueGraph source outside).minDegree) := by
    simpa only [PackedMinimumDegreeCycle.StaticInput.problem, glue,
      FiniteObject.minDegree] using sourceBaseline
  have replacementBaseline := glue_preserves_minDegree boundaries
    input.minimumDegree source replacement outside profileEq internal
    sourceBaseline'
  simpa only [PackedMinimumDegreeCycle.StaticInput.problem, glue,
    FiniteObject.minDegree] using replacementBaseline

/-- Boundary-degree profile used by the literal replacement theorem. -/
def BoundaryDegreeProfile (piece : Piece T) : T → Nat :=
  piece.boundaryDegree boundaries

/-- Universal equality of target response against every literal outside
context. -/
def ContextEquivalent (left right : Piece T) : Prop :=
  ∀ outside : Context T,
    input.Target (glue boundaries left outside) ↔
      input.Target (glue boundaries right outside)

/-- Exact target-completeness for literal pieces. -/
def TargetComplete (left right : Piece T) : Prop :=
  BoundaryDegreeProfile boundaries left =
      BoundaryDegreeProfile boundaries right ∧
    ContextEquivalent input boundaries left right

/-- A concrete context witnessing failure of target equivalence. -/
def TargetDefective (left right : Piece T) : Prop :=
  ∃ outside : Context T,
    ¬ (input.Target (glue boundaries left outside) ↔
      input.Target (glue boundaries right outside))

omit [Nonempty T] in
theorem boundaryDegreeProfile_ne_not_targetComplete {left right : Piece T}
    (different : BoundaryDegreeProfile boundaries left ≠
      BoundaryDegreeProfile boundaries right) :
    ¬ TargetComplete input boundaries left right := by
  intro complete
  exact different complete.1

omit [Nonempty T] in
theorem targetComplete_contextUniversal {left right : Piece T}
    (complete : TargetComplete input boundaries left right) :
    ContextEquivalent input boundaries left right :=
  complete.2

omit [Nonempty T] in
theorem targetComplete_trans {first second third : Piece T}
    (firstSecond : TargetComplete input boundaries first second)
    (secondThird : TargetComplete input boundaries second third) :
    TargetComplete input boundaries first third := by
  refine ⟨firstSecond.1.trans secondThird.1, ?_⟩
  intro outside
  exact (firstSecond.2 outside).trans (secondThird.2 outside)

omit [Nonempty T] in
theorem targetDefective_of_not_contextEquivalent {left right : Piece T}
    (failure : ¬ ContextEquivalent input boundaries left right) :
    TargetDefective input boundaries left right := by
  simpa only [ContextEquivalent, TargetDefective, not_forall] using failure

/-- One actual atom decomposition, reconstructed up to graph isomorphism, so
no equality between packed sigma types is required. -/
structure ProperAtom
    (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target) where
  source : Piece T
  outside : Context T
  reconstruct :
    (glue boundaries source outside).object.graph ≃g ctx.G.object.graph
  connected : source.graph.Connected
  proper : (Piece.pack boundaries source).lexRank < ctx.G.lexRank

/-- A concrete manuscript replacement.  It assumes only one-way obstruction
inclusion; target-complete compression is a derived special case.  The only
size hypothesis is local lexicographic decrease of the replacement piece. -/
structure Compression
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    (atom : ProperAtom input boundaries ctx) where
  piece : Piece T
  boundaryDegree_eq : ∀ boundary,
    piece.boundaryDegree boundaries boundary =
      atom.source.boundaryDegree boundaries boundary
  obstructionIncluded : ∀ outside : Context T,
    input.Target (glue boundaries piece outside) →
      input.Target (glue boundaries atom.source outside)
  internalTargetFree :
    ¬ input.Target (Piece.pack boundaries piece)
  internalBaseline :
    piece.InternalBaseline boundaries input.minimumDegree
  locallySmaller : Piece.LexSmaller piece atom.source

/-- A target-complete compression is a special case of the one-way
replacement relation required by the manuscript lemma. -/
noncomputable def Compression.ofTargetComplete
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    {atom : ProperAtom input boundaries ctx} (piece : Piece T)
    (complete : TargetComplete input boundaries piece atom.source)
    (internalTargetFree :
      ¬ input.Target (Piece.pack boundaries piece))
    (internalBaseline : piece.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller piece atom.source) :
    Compression input boundaries atom where
  piece := piece
  boundaryDegree_eq := congrFun complete.1
  obstructionIncluded := fun outside replacementTarget =>
    (complete.2 outside).mp replacementTarget
  internalTargetFree := internalTargetFree
  internalBaseline := internalBaseline
  locallySmaller := locallySmaller

namespace Compression

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {atom : ProperAtom input boundaries ctx}

/-- The certified CT3 reduction derived entirely from literal gluing,
isomorphism transport, and the local compression data. -/
noncomputable def certifiedInput (compression : Compression input boundaries atom) :
    CT3.CertifiedCompressionInput ctx where
  reduction := {
    value := glue boundaries compression.piece atom.outside
    decreases := by
      calc
        (glue boundaries compression.piece atom.outside).lexRank <
            (glue boundaries atom.source atom.outside).lexRank :=
          glue_lexRank_lt boundaries atom.outside compression.locallySmaller
        _ = ctx.G.lexRank := lexRank_eq_of_iso atom.reconstruct
  }
  reducedBaseline := by
    apply glue_preserves_problemBaseline input boundaries atom.source
      compression.piece atom.outside compression.boundaryDegree_eq
      compression.internalBaseline
    exact (minDegree_iff_of_iso atom.reconstruct input.minimumDegree).2
      ctx.baseline
  targetMonotone := by
    intro replacementTarget
    have sourceTarget := compression.obstructionIncluded atom.outside
      replacementTarget
    exact (hasCycleWithLength_iff_of_iso atom.reconstruct input.LengthOK).mp
      sourceTarget

noncomputable def run (compression : Compression input boundaries atom) :
    CT3.CertifiedCompressionRun ctx compression.certifiedInput :=
  CT3.runCertifiedCompression ctx compression.certifiedInput

theorem impossible (compression : Compression input boundaries atom) : False :=
  (run compression).verified

theorem run_terminal (compression : Compression input boundaries atom) :
    (run compression).terminal = .compression := rfl

theorem run_trace (compression : Compression input boundaries atom) :
    (run compression).trace =
      [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] := rfl

theorem run_checks (compression : Compression input boundaries atom) :
    (run compression).checks = 1 := rfl

theorem run_polynomial (compression : Compression input boundaries atom) :
    (run compression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            compression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree := by
  simp [run_checks, CT3.certifiedCompressionBudget,
    Core.PolynomialCheckBudget.constant]

theorem run_total (compression : Compression input boundaries atom) :
    ∃ result : CT3.CertifiedCompressionRun ctx compression.certifiedInput,
      result.terminal = .compression ∧
        result.trace = [.entry, .vectorComputation, .compressionSearch,
          .compressionTerminal] :=
  CT3.runCertifiedCompression_total ctx compression.certifiedInput

end Compression

/-- Universal airtight CT3 result for every literal normalized atom and every
locally smaller obstruction-preserving replacement. -/
structure VerifiedStage
    (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target) : Prop where
  compressionImpossible : ∀ (atom : ProperAtom input boundaries ctx)
    (_compression : Compression input boundaries atom), False
  terminal : ∀ (atom : ProperAtom input boundaries ctx)
    (compression : Compression input boundaries atom),
    (Compression.run compression).terminal = .compression
  trace : ∀ (atom : ProperAtom input boundaries ctx)
    (compression : Compression input boundaries atom),
    (Compression.run compression).trace = [.entry, .vectorComputation, .compressionSearch,
      .compressionTerminal]
  checks : ∀ (atom : ProperAtom input boundaries ctx)
    (compression : Compression input boundaries atom),
    (Compression.run compression).checks = 1
  polynomial : ∀ (atom : ProperAtom input boundaries ctx)
    (compression : Compression input boundaries atom),
    (Compression.run compression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            compression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree

noncomputable def verifiedStage
    (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target) :
    VerifiedStage input boundaries ctx where
  compressionImpossible := fun _atom compression => compression.impossible
  terminal := fun _atom compression => compression.run_terminal
  trace := fun _atom compression => compression.run_trace
  checks := fun _atom compression => compression.run_checks
  polynomial := fun _atom compression => compression.run_polynomial

end MinimumDegreeCycleReplacement

end StructuralExhaustion.Graph.PackedBoundariedGluing
