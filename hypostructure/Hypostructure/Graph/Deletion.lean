import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Hypostructure.Graph.Induced

/-!
# Primitive finite graph deletions

Vertex deletion is induced restriction to the erased full support.  Edge
deletion removes one certified Mathlib edge and retains the incoming vertex
schedule.  Neither operation carries a baseline or target assumption.
-/

namespace Hypostructure.Graph

namespace FiniteObject

/-- Delete one certified undirected edge while retaining every vertex. -/
def deleteEdge (object : FiniteObject) (edge : object.graph.edgeSet) :
    FiniteObject where
  Vertex := object.Vertex
  graph := object.graph.deleteEdges {edge.1}
  vertices := object.vertices
  decideAdj := by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel object.graph.Adj := object.decideAdj
    infer_instance

@[simp]
theorem deleteEdge_adj (object : FiniteObject)
    (edge : object.graph.edgeSet) (left right : object.Vertex) :
    (object.deleteEdge edge).graph.Adj left right ↔
      object.graph.Adj left right ∧ s(left, right) ≠ edge.1 := by
  simp [deleteEdge]

theorem deleteEdge_le (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).graph ≤ object.graph :=
  object.graph.deleteEdges_le {edge.1}

@[simp]
theorem vertexCount_deleteEdge (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).vertexCount = object.vertexCount :=
  rfl

/-- Deleting a certified edge decreases the edge count by exactly one. -/
theorem edgeCount_deleteEdge_add_one (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).edgeCount + 1 = object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {edge.1}).edgeFinset.card + 1 =
    object.graph.edgeFinset.card
  have edgeFinsetEq :
      (object.graph.deleteEdges {edge.1}).edgeFinset =
        object.graph.edgeFinset.erase edge.1 := by
    ext other
    simp [SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [edgeFinsetEq]
  exact Finset.card_erase_add_one
    (SimpleGraph.mem_edgeFinset.mpr edge.2)

theorem edgeCount_deleteEdge_lt (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).edgeCount < object.edgeCount := by
  have exactDrop := object.edgeCount_deleteEdge_add_one edge
  omega

/-- Delete a vertex by inducing on the erased full support. -/
def deleteVertex (object : FiniteObject) (vertex : object.Vertex) :
    FiniteObject :=
  object.induce
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

/-- Canonical embedding of a vertex-deleted graph into its source. -/
def deleteVertexEmbedding (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).graph ↪g object.graph :=
  object.induceEmbedding
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

theorem deleteVertex_le (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).graph.map
        (object.deleteVertexEmbedding vertex).toEmbedding ≤ object.graph :=
  object.induce_le
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

/-- Deleting one vertex decreases the vertex count by exactly one. -/
theorem vertexCount_deleteVertex_add_one (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).vertexCount + 1 = object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  rw [deleteVertex, vertexCount_induce]
  simpa [object.card_vertexFinset] using
    Finset.card_erase_add_one (object.mem_vertexFinset vertex)

/-- Vertex deletion removes exactly the edges incident with that vertex. -/
theorem edgeCount_deleteVertex (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).edgeCount =
      object.edgeCount - object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have supportEq :
      ((@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Finset object.Vertex) :
          Set object.Vertex) = ({vertex}ᶜ : Set object.Vertex) := by
    ext other
    simp [vertexFinset]
  rw [(object.deleteVertex vertex).edgeCount_eq_ncard_edgeSet,
    object.edgeCount_eq_ncard_edgeSet,
    object.degree_eq_ncard_neighborSet]
  change (object.graph.induce
      ((@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Finset object.Vertex) :
        Set object.Vertex)).edgeSet.ncard =
    object.graph.edgeSet.ncard - (object.graph.neighborSet vertex).ncard
  rw [supportEq]
  let complement :=
    object.graph.induce ({vertex}ᶜ : Set object.Vertex)
  have exactCount :
      complement.edgeFinset.card =
        object.graph.edgeFinset.card - object.graph.degree vertex := by
    rw [object.graph.card_edgeFinset_induce_compl_singleton,
      object.graph.card_edgeFinset_deleteIncidenceSet]
  have complementBridge :
      complement.edgeSet.ncard = complement.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have sourceBridge :
      object.graph.edgeSet.ncard = object.graph.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have degreeBridge :
      (object.graph.neighborSet vertex).ncard =
        object.graph.degree vertex := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  calc
    complement.edgeSet.ncard = complement.edgeFinset.card := complementBridge
    _ = object.graph.edgeFinset.card - object.graph.degree vertex := exactCount
    _ = object.graph.edgeSet.ncard -
        (object.graph.neighborSet vertex).ncard := by
      rw [sourceBridge, degreeBridge]

end FiniteObject

end Hypostructure.Graph
