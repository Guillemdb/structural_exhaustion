import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Graph.Boundary
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.Problem

/-!
# Exact boundary gluing

Graph supplies the literal union and its reconstruction isomorphism.  The
resulting adapter is a `Core.AtomContextAssembly`; replacement and every later
decision or route remain Core-owned.
-/

namespace Hypostructure.Graph

universe u v

/-- Identify common boundary labels and take the union of the two owned sides. -/
def glueGraph {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph (GluedVertex piece outside) :=
  piece.graph.map (pieceEmbedding piece outside) ⊔
    outside.graph.map (contextEmbedding piece outside)

/-- Adjacency in a gluing is exactly adjacency owned by one finite side. -/
theorem glueGraph_adj_iff {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : GluedVertex piece outside) :
    (glueGraph piece outside).Adj left right <->
      OwnedAdjacency piece outside left right := by
  rw [glueGraph]
  constructor
  · rintro (pieceAdjacent | contextAdjacent)
    · exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph left right).mp pieceAdjacent)
    · exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph left right).mp contextAdjacent)
  · rintro (pieceAdjacent | contextAdjacent)
    · exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph left right).mpr pieceAdjacent)
    · exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph left right).mpr contextAdjacent)

/-- The glued graph with its finite schedule derived from the three disjoint
vertex families.
-/
noncomputable def glue {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    FiniteObject.{u} where
  Vertex := GluedVertex piece outside
  graph := glueGraph piece outside
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum piece.Internal := piece.internalVertices
    letI : FinEnum outside.Internal := outside.internalVertices
    infer_instance
  decideAdj := Classical.decRel _

/-- Exact vertex accounting for a literal gluing. -/
@[simp]
theorem glue_vertexCount {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (glue piece outside).vertexCount =
      boundary.vertexCount + piece.internalVertexCount +
        outside.internalVertexCount := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  simp [glue, FiniteObject.vertexCount, Boundary.vertexCount,
    BoundaryPiece.internalVertexCount, OutsideContext.internalVertexCount,
    FinEnum.card_eq_fintypeCard, Nat.add_assoc]

namespace OwnedDecomposition

/-- The exact ownership law reconstructs the ambient graph up to isomorphism. -/
def reconstructionIso {object : FiniteObject.{u}}
    (site : OwnedDecomposition object) :
    (glue site.piece site.outside).Iso object where
  toEquiv := site.vertexEquiv
  map_rel_iff' := by
    intro left right
    exact ((glueGraph_adj_iff site.piece site.outside left right).trans
      (site.ownsAdjacency left right).symm).symm

end OwnedDecomposition

/-- Register finite boundary decomposition as the generic Core assembly API. -/
noncomputable def boundaryAssembly
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline) :
    Core.AtomContextAssembly
      (problem Baseline BranchState)
      (isomorphismEquivalence Baseline BranchState baselineInvariant) where
  Interface := Boundary.{u}
  Site := OwnedDecomposition
  interface := fun _ site => site.interface
  Atom := BoundaryPiece
  Context := OutsideContext
  compatible := fun _ _ => True
  atom := fun _ site => site.piece
  context := fun _ site => site.outside
  assemble := fun piece outside => glue piece outside
  extractedCompatible := fun _ _ => True.intro
  reconstruct := fun _ site => ⟨site.reconstructionIso⟩

end Hypostructure.Graph
