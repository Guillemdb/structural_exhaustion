import Hypostructure.Core.Coordinate.Transport
import Hypostructure.Graph.Coordinate
import Hypostructure.Graph.Gluing

/-!
# Graph coordinate and assembly fixtures

The local and outside pieces are single edges sharing one labelled boundary.
Their gluing has three vertices.  The same file exercises a Core-owned graph
coordinate path and composite baseline transport.
-/

namespace Hypostructure.Fixtures.GraphAssembly

open Hypostructure.Graph

/-- One labelled boundary vertex. -/
def boundary : Boundary where
  Vertex := Unit
  vertices := inferInstance

/-- One boundary--internal edge. -/
def piece : BoundaryPiece boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

/-- One boundary--outside edge. -/
def outside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

/-- Relabel the common boundary as vertex `1`, the atom interior as `0`, and
the outside interior as `2`.
-/
def gluedToFinThree : GluedVertex piece outside ≃ Fin 3 where
  toFun
    | .inl _ => 1
    | .inr (.inl _) => 0
    | .inr (.inr _) => 2
  invFun vertex :=
    if vertex = 0 then
      .inr (.inl ())
    else if vertex = 1 then
      .inl ()
    else
      .inr (.inr ())
  left_inv := by
    intro vertex
    change Unit ⊕ (Unit ⊕ Unit) at vertex
    rcases vertex with (⟨⟩ | (⟨⟩ | ⟨⟩)) <;> rfl
  right_inv := by
    intro vertex
    fin_cases vertex <;> simp

/-- An independently packed relabelling of the literal gluing. -/
noncomputable def ambient : FiniteObject where
  Vertex := Fin 3
  graph := (glueGraph piece outside).map gluedToFinThree.toEmbedding
  vertices := inferInstance
  decideAdj := Classical.decRel _

/-- Exact decomposition of the fixture ambient graph. -/
noncomputable def site : OwnedDecomposition ambient where
  interface := boundary
  piece := piece
  outside := outside
  vertexEquiv := gluedToFinThree
  ownsAdjacency := by
    intro left right
    change ((glueGraph piece outside).map gluedToFinThree.toEmbedding).Adj
      (gluedToFinThree left) (gluedToFinThree right) <->
      OwnedAdjacency piece outside left right
    simpa only [Equiv.toEmbedding_apply] using
      ((SimpleGraph.map_adj_apply
        (G := glueGraph piece outside)
        (f := gluedToFinThree.toEmbedding)
        (a := left) (b := right)).trans
          (glueGraph_adj_iff piece outside left right))

def Baseline (_ : FiniteObject) : Prop := True

def BranchState (_ : FiniteObject) := Unit

def baselineInvariant : FiniteObject.IsomorphismInvariant Baseline where
  iff_of_iso := by simp [Baseline]

noncomputable def assembly :=
  boundaryAssembly Baseline BranchState baselineInvariant

theorem ambient_vertexCount : ambient.vertexCount = 3 := by
  rfl

theorem assembled_vertexCount : (glue piece outside).vertexCount = 3 := by
  rw [glue_vertexCount]
  decide

/-- Core receives the graph reconstruction as semantic equivalence. -/
theorem assembly_reconstructs :
    (isomorphismEquivalence Baseline BranchState baselineInvariant).equivalent
      (assembly.assemble (assembly.atom ambient site)
        (assembly.context ambient site)) ambient :=
  assembly.reconstruct ambient site

/-! ## A context-owned boundary edge -/

/-- Two boundary labels and no internal vertices on either side isolate the
boundary-edge ownership law from all other graph structure. -/
def edgeBoundary : Boundary where
  Vertex := Fin 2
  vertices := inferInstance

/-- The local side has no edge between the two boundary labels. -/
def boundaryEmptyPiece : BoundaryPiece edgeBoundary where
  Internal := Empty
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by infer_instance

/-- The outside context contributes the edge between the two boundary labels. -/
def boundaryEdgeOutside : OutsideContext edgeBoundary where
  Internal := Empty
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq edgeBoundary.Vertex := edgeBoundary.vertices.decEq
    infer_instance

/-- With no internal vertices, identifying the common boundary leaves the
two-element boundary carrier. -/
def boundaryEdgeGluedToFinTwo :
    GluedVertex boundaryEmptyPiece boundaryEdgeOutside ≃ Fin 2 where
  toFun
    | .inl vertex => vertex
    | .inr (.inl vertex) => nomatch vertex
    | .inr (.inr vertex) => nomatch vertex
  invFun vertex := .inl vertex
  left_inv := by
    intro vertex
    rcases vertex with vertex | (vertex | vertex)
    · rfl
    · exact Empty.elim vertex
    · exact Empty.elim vertex
  right_inv := by
    intro vertex
    rfl

/-- A finite ambient relabelling of the gluing with the context-owned boundary
edge. -/
noncomputable def boundaryEdgeAmbient : FiniteObject where
  Vertex := Fin 2
  graph := (glueGraph boundaryEmptyPiece boundaryEdgeOutside).map
    boundaryEdgeGluedToFinTwo.toEmbedding
  vertices := inferInstance
  decideAdj := Classical.decRel _

/-- Exact decomposition of the ambient boundary-edge fixture. -/
noncomputable def boundaryEdgeSite : OwnedDecomposition boundaryEdgeAmbient where
  interface := edgeBoundary
  piece := boundaryEmptyPiece
  outside := boundaryEdgeOutside
  vertexEquiv := boundaryEdgeGluedToFinTwo
  ownsAdjacency := by
    intro left right
    change ((glueGraph boundaryEmptyPiece boundaryEdgeOutside).map
      boundaryEdgeGluedToFinTwo.toEmbedding).Adj
        (boundaryEdgeGluedToFinTwo left) (boundaryEdgeGluedToFinTwo right) <->
      OwnedAdjacency boundaryEmptyPiece boundaryEdgeOutside left right
    simpa only [Equiv.toEmbedding_apply] using
      ((SimpleGraph.map_adj_apply
        (G := glueGraph boundaryEmptyPiece boundaryEdgeOutside)
        (f := boundaryEdgeGluedToFinTwo.toEmbedding)
        (a := left) (b := right)).trans
          (glueGraph_adj_iff boundaryEmptyPiece boundaryEdgeOutside left right))

/-- The outside context literally owns its boundary--boundary edge. -/
theorem boundaryEdgeOutside_owns_edge :
    boundaryEdgeOutside.graph.Adj
      (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) := by
  apply (SimpleGraph.top_adj _ _).mpr
  intro equality
  have impossible : (0 : Fin 2) = 1 := Sum.inl.inj equality
  exact (by decide : Not ((0 : Fin 2) = 1)) impossible

/-- The local side does not own that edge. -/
theorem boundaryEmptyPiece_avoids_edge :
    Not (boundaryEmptyPiece.graph.Adj
      (.inl (0 : Fin 2)) (.inl (1 : Fin 2))) := by
  simp [boundaryEmptyPiece]

/-- Union gluing retains an edge owned only by the outside context. -/
theorem boundaryEdge_glued_adjacent :
    (glueGraph boundaryEmptyPiece boundaryEdgeOutside).Adj
      (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) := by
  rw [glueGraph_adj_iff]
  exact Or.inr ⟨.inl (0 : Fin 2), .inl (1 : Fin 2),
    boundaryEdgeOutside_owns_edge, rfl, rfl⟩

/-- Exact ownership reconstructs the finite ambient graph even when the
outside owns a boundary--boundary edge. -/
noncomputable def boundaryEdgeReconstructionIso :
    (glue boundaryEdgeSite.piece boundaryEdgeSite.outside).Iso
      boundaryEdgeAmbient :=
  boundaryEdgeSite.reconstructionIso

/-- A four-vertex complete graph used by the coordinate fixture. -/
abbrev k4 : FiniteObject where
  Vertex := Fin 4
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def firstThree : Finset (Fin 4) := {0, 1, 2}

def swapFirstTwoIso : k4.Iso k4 := by
  change (⊤ : SimpleGraph (Fin 4)) ≃g (⊤ : SimpleGraph (Fin 4))
  exact SimpleGraph.Iso.completeGraph (Equiv.swap 0 1)

def coordinates := coordinateSystem Baseline BranchState

def coordinatePath :
    Core.CoordinatePath coordinates k4 (k4.induce firstThree) :=
  .cons (.relabel swapFirstTwoIso)
    (.cons (.induce k4 firstThree) .nil)

def baselineLaws : Core.PrimitiveBaselineTransport coordinates :=
  CoordinatePrimitive.baselineTransport Baseline BranchState baselineInvariant
    (by simp [Baseline])

/-- Baseline transport is composed by Core across relabelling and restriction. -/
theorem coordinate_path_preserves_baseline :
    Baseline ((coordinates.realize (k4.induce firstThree))
      (coordinatePath.run ())) := by
  exact coordinatePath.transportBaseline baselineLaws () (by trivial)

#print axioms ambient_vertexCount
#print axioms assembled_vertexCount
#print axioms OwnedDecomposition.reconstructionIso
#print axioms assembly_reconstructs
#print axioms boundaryEdgeOutside_owns_edge
#print axioms boundaryEmptyPiece_avoids_edge
#print axioms boundaryEdge_glued_adjacent
#print axioms boundaryEdgeReconstructionIso
#print axioms coordinate_path_preserves_baseline

end Hypostructure.Fixtures.GraphAssembly
