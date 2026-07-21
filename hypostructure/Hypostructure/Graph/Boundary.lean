import Hypostructure.Graph.Finite

/-!
# Finite graph boundaries

The piece owns all boundary--boundary edges.  A normalized outside context
owns none, so the two finite sides have an exact, disjoint ownership convention
when they are glued.  The structures contain no target, obstruction, or
problem-specific state.
-/

namespace Hypostructure.Graph

universe u

/-- A finite labelled interface. -/
structure Boundary where
  Vertex : Type u
  vertices : FinEnum Vertex

namespace Boundary

/-- Number of interface labels, derived from the supplied finite schedule. -/
def vertexCount (boundary : Boundary.{u}) : Nat :=
  boundary.vertices.card

end Boundary

/-- The atom side of a graph decomposition.  It owns boundary--boundary edges. -/
structure BoundaryPiece (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj

/-- The normalized global context.  Its boundary--boundary edge set is empty. -/
structure OutsideContext (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj
  noBoundaryEdge : forall left right : boundary.Vertex,
    Not (graph.Adj (.inl left) (.inl right))

namespace BoundaryPiece

/-- Internal size is the replacement-relevant vertex count. -/
def internalVertexCount {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) : Nat :=
  piece.internalVertices.card

/-- Forget the distinguished interface and obtain an ordinary finite graph. -/
def pack {boundary : Boundary.{u}} (piece : BoundaryPiece boundary) :
    FiniteObject.{u} where
  Vertex := boundary.Vertex ⊕ piece.Internal
  graph := piece.graph
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum piece.Internal := piece.internalVertices
    infer_instance
  decideAdj := piece.decideAdj

end BoundaryPiece

namespace OutsideContext

/-- Internal size of the outside context. -/
def internalVertexCount {boundary : Boundary.{u}}
    (outside : OutsideContext boundary) : Nat :=
  outside.internalVertices.card

/-- Forget the interface normalization and obtain an ordinary finite graph. -/
def pack {boundary : Boundary.{u}} (outside : OutsideContext boundary) :
    FiniteObject.{u} where
  Vertex := boundary.Vertex ⊕ outside.Internal
  graph := outside.graph
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum outside.Internal := outside.internalVertices
    infer_instance
  decideAdj := outside.decideAdj

end OutsideContext

/-- Common vertex type obtained by identifying equal boundary labels. -/
abbrev GluedVertex {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :=
  boundary.Vertex ⊕ (piece.Internal ⊕ outside.Internal)

/-- Canonical inclusion of atom vertices into the glued carrier. -/
def pieceEmbedding {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (boundary.Vertex ⊕ piece.Internal) ↪ GluedVertex piece outside where
  toFun
    | .inl vertex => .inl vertex
    | .inr vertex => .inr (.inl vertex)
  inj' := by
    intro left right equality
    cases left <;> cases right <;> simp_all

/-- Canonical inclusion of context vertices into the glued carrier. -/
def contextEmbedding {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (boundary.Vertex ⊕ outside.Internal) ↪ GluedVertex piece outside where
  toFun
    | .inl vertex => .inl vertex
    | .inr vertex => .inr (.inr vertex)
  inj' := by
    intro left right equality
    cases left <;> cases right <;> simp_all

/-- One glued adjacency contributed by the atom side. -/
def PieceOwns {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : GluedVertex piece outside) : Prop :=
  Exists fun pieceLeft => Exists fun pieceRight =>
    piece.graph.Adj pieceLeft pieceRight /\
      pieceEmbedding piece outside pieceLeft = left /\
      pieceEmbedding piece outside pieceRight = right

/-- One glued adjacency contributed by the normalized context side. -/
def ContextOwns {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : GluedVertex piece outside) : Prop :=
  Exists fun contextLeft => Exists fun contextRight =>
    outside.graph.Adj contextLeft contextRight /\
      contextEmbedding piece outside contextLeft = left /\
      contextEmbedding piece outside contextRight = right

/-- Exact local ownership predicate for an edge of a glued carrier. -/
def OwnedAdjacency {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : GluedVertex piece outside) : Prop :=
  PieceOwns piece outside left right ∨ ContextOwns piece outside left right

/-- A site in an ambient graph, specified by a vertex partition and one exact
adjacency ownership law.  All finite schedules and side embeddings are derived
from the interface, piece, context, and vertex equivalence.
-/
structure OwnedDecomposition (object : FiniteObject.{u}) where
  interface : Boundary.{u}
  piece : BoundaryPiece interface
  outside : OutsideContext interface
  vertexEquiv : GluedVertex piece outside ≃ object.Vertex
  ownsAdjacency : forall left right,
    object.graph.Adj (vertexEquiv left) (vertexEquiv right) <->
      OwnedAdjacency piece outside left right

end Hypostructure.Graph
