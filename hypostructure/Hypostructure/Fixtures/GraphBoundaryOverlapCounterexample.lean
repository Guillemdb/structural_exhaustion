import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Hypostructure.Graph.BoundariedAtom

/-!
# Boundary-edge overlap counterexample

This fixture isolates the residual in `original_erdos_64_proof.tex`, line 5619.
Under unrestricted union gluing, equality of the uncapped piece-local boundary
degree profiles does not imply equality of the final glued boundary degrees.

The same example also shows why local edge progress need not become global edge
progress: the outside boundary edge overlaps the source but not the replacement.
-/

namespace Hypostructure.Fixtures.GraphBoundaryOverlapCounterexample

open Hypostructure.Graph

abbrev BoundaryVertex := Fin 4
abbrev InternalVertex := Fin 3
abbrev PieceVertex := BoundaryVertex ⊕ InternalVertex

abbrev boundary : Boundary where
  Vertex := BoundaryVertex
  vertices := inferInstance

/-! The common six-edge connected spine is
`0-2-1-3`, together with `0-a`, `1-b`, and `2-c`. -/

def commonForwardEdge : PieceVertex → PieceVertex → Bool
  | .inl left, .inl right =>
      (left == 0 && right == 2) ||
      (left == 2 && right == 1) ||
      (left == 1 && right == 3)
  | .inl left, .inr right =>
      (left == 0 && right == 0) ||
      (left == 1 && right == 1) ||
      (left == 2 && right == 2)
  | _, _ => false

/-! The source adds the boundary edge `0-1` and two internal edges. -/

def sourceForwardEdge (left right : PieceVertex) : Bool :=
  commonForwardEdge left right ||
    (left == .inl 0 && right == .inl 1) ||
    (left == .inr 0 && right == .inr 1) ||
    (left == .inr 1 && right == .inr 2)

abbrev sourceGraph : SimpleGraph PieceVertex :=
  SimpleGraph.fromRel fun left right => sourceForwardEdge left right

abbrev source : BoundaryPiece boundary where
  Internal := InternalVertex
  internalVertices := inferInstance
  graph := sourceGraph
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    dsimp [sourceGraph]
    infer_instance

/-! The replacement omits `0-1` and compensates locally with `0-b` and `1-c`.
It therefore has the same boundary profile but one fewer local edge. -/

def replacementForwardEdge (left right : PieceVertex) : Bool :=
  commonForwardEdge left right ||
    (left == .inl 0 && right == .inr 1) ||
    (left == .inl 1 && right == .inr 2)

abbrev replacementGraph : SimpleGraph PieceVertex :=
  SimpleGraph.fromRel fun left right => replacementForwardEdge left right

abbrev replacement : BoundaryPiece boundary where
  Internal := InternalVertex
  internalVertices := inferInstance
  graph := replacementGraph
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    dsimp [replacementGraph]
    infer_instance

/-! The unrestricted outside context owns precisely the boundary edge `0-1`. -/

abbrev OutsideVertex := BoundaryVertex ⊕ Empty

def outsideForwardEdge (left right : OutsideVertex) : Bool :=
  left == .inl 0 && right == .inl 1

abbrev outsideGraph : SimpleGraph OutsideVertex :=
  SimpleGraph.fromRel fun left right => outsideForwardEdge left right

abbrev outside : OutsideContext boundary where
  Internal := Empty
  internalVertices := inferInstance
  graph := outsideGraph
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    dsimp [outsideGraph]
    infer_instance

theorem source_connected : source.graph.Connected := by
  change sourceGraph.Connected
  decide

theorem replacement_connected : replacement.graph.Connected := by
  change replacementGraph.Connected
  decide

/-- Both connected pieces have the exact uncapped profile `(3, 4, 3, 1)`. -/
theorem identical_uncapped_boundaryDegreeProfile :
    (source.boundaryDegreeProfile : BoundaryVertex → Nat) =
      (replacement.boundaryDegreeProfile : BoundaryVertex → Nat) := by
  funext vertex
  change sourceGraph.degree (.inl vertex) =
    replacementGraph.degree (.inl vertex)
  fin_cases vertex <;> decide

theorem source_owns_context_edge :
    source.graph.Adj (.inl (0 : BoundaryVertex)) (.inl (1 : BoundaryVertex)) := by
  change sourceGraph.Adj (.inl 0) (.inl 1)
  decide

theorem replacement_avoids_context_edge :
    ¬ replacement.graph.Adj
      (.inl (0 : BoundaryVertex)) (.inl (1 : BoundaryVertex)) := by
  change ¬ replacementGraph.Adj (.inl 0) (.inl 1)
  decide

theorem outside_owns_boundary_edge :
    outside.graph.Adj
      (.inl (0 : BoundaryVertex)) (.inl (1 : BoundaryVertex)) := by
  change outsideGraph.Adj (.inl 0) (.inl 1)
  decide

/-! These finite objects retain the literal current `glueGraph`; only their
adjacency deciders are made computational so the fixture can audit degrees. -/

@[reducible]
def sourceGlueDecideAdj : DecidableRel (glueGraph source outside).Adj := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum source.Internal := source.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : DecidableRel source.graph.Adj := source.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  intro left right
  letI : Decidable (OwnedAdjacency source outside left right) := by
    unfold OwnedAdjacency PieceOwns ContextOwns
    infer_instance
  exact decidable_of_iff (OwnedAdjacency source outside left right)
    (glueGraph_adj_iff source outside left right).symm

@[reducible]
def replacementGlueDecideAdj :
    DecidableRel (glueGraph replacement outside).Adj := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum replacement.Internal := replacement.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  letI : DecidableRel replacement.graph.Adj := replacement.decideAdj
  letI : DecidableRel outside.graph.Adj := outside.decideAdj
  intro left right
  letI : Decidable (OwnedAdjacency replacement outside left right) := by
    unfold OwnedAdjacency PieceOwns ContextOwns
    infer_instance
  exact decidable_of_iff (OwnedAdjacency replacement outside left right)
    (glueGraph_adj_iff replacement outside left right).symm

abbrev sourceGluing : FiniteObject where
  Vertex := GluedVertex source outside
  graph := glueGraph source outside
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum source.Internal := source.internalVertices
    letI : FinEnum outside.Internal := outside.internalVertices
    infer_instance
  decideAdj := sourceGlueDecideAdj

abbrev replacementGluing : FiniteObject where
  Vertex := GluedVertex replacement outside
  graph := glueGraph replacement outside
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum replacement.Internal := replacement.internalVertices
    letI : FinEnum outside.Internal := outside.internalVertices
    infer_instance
  decideAdj := replacementGlueDecideAdj

/-- The equal local profiles do not survive gluing: at boundary vertex `0`,
the source has degree `3`, while the replacement gluing has degree `4`. -/
theorem source_glued_boundary_degree_zero :
    sourceGluing.degree (.inl (0 : BoundaryVertex)) = 3 := by
  decide

theorem replacement_glued_boundary_degree_zero :
    replacementGluing.degree (.inl (0 : BoundaryVertex)) = 4 := by
  decide

theorem glued_boundary_degrees_differ :
    sourceGluing.degree (.inl (0 : BoundaryVertex)) ≠
      replacementGluing.degree (.inl (0 : BoundaryVertex)) := by
  decide

/-- Locally, the replacement is strictly smaller: both sides have three
internal vertices, while their local edge counts are `8 < 9`. -/
theorem source_edgeCount : source.edgeCount = 9 := by
  change sourceGraph.edgeFinset.card = 9
  decide

theorem replacement_edgeCount : replacement.edgeCount = 8 := by
  change replacementGraph.edgeFinset.card = 8
  decide

theorem replacement_locallySmaller_source :
    replacement.LocallySmaller source := by
  rw [BoundaryPiece.locallySmaller_iff]
  right
  constructor
  · rfl
  · rw [replacement_edgeCount, source_edgeCount]
    decide

/-- Globally, that strict edge decrease disappears. The context edge is already
owned by the source but is newly added to the replacement, so both gluings have
nine edges. -/
theorem source_glued_edgeCount : sourceGluing.edgeCount = 9 := by
  decide

theorem replacement_glued_edgeCount : replacementGluing.edgeCount = 9 := by
  decide

theorem local_progress_does_not_lower_glued_edgeCount :
    replacementGluing.edgeCount = sourceGluing.edgeCount := by
  decide

#print axioms source_connected
#print axioms replacement_connected
#print axioms identical_uncapped_boundaryDegreeProfile
#print axioms outside_owns_boundary_edge
#print axioms glued_boundary_degrees_differ
#print axioms replacement_locallySmaller_source
#print axioms local_progress_does_not_lower_glued_edgeCount

end Hypostructure.Fixtures.GraphBoundaryOverlapCounterexample
