import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Hypostructure.Graph.Object

/-!
# Finite graph observables

All finite views are derived from `FiniteObject.vertices`; applications do not
register duplicate cardinality, degree, edge, or neighbour data.
-/

namespace Hypostructure.Graph

namespace FiniteObject

/-- Vertices in the object's declared scan order. -/
def orderedVertices (object : FiniteObject) : List object.Vertex :=
  @FinEnum.toList object.Vertex object.vertices

@[simp]
theorem mem_orderedVertices (object : FiniteObject) (vertex : object.Vertex) :
    vertex ∈ object.orderedVertices := by
  exact @FinEnum.mem_toList object.Vertex object.vertices vertex

theorem orderedVertices_nodup (object : FiniteObject) :
    object.orderedVertices.Nodup := by
  exact @FinEnum.nodup_toList object.Vertex object.vertices

@[simp]
theorem orderedVertices_length (object : FiniteObject) :
    object.orderedVertices.length = object.vertices.card := by
  letI : FinEnum object.Vertex := object.vertices
  simp [orderedVertices, FinEnum.toList]

/-- Number of vertices in the declared finite schedule. -/
def vertexCount (object : FiniteObject) : Nat :=
  object.vertices.card

@[simp]
theorem vertexCount_eq_orderedVertices_length (object : FiniteObject) :
    object.vertexCount = object.orderedVertices.length := by
  rw [orderedVertices_length]
  rfl

/-- The full finite support associated with the declared vertex schedule. -/
def vertexFinset (object : FiniteObject) : Finset object.Vertex :=
  @Finset.univ object.Vertex (@FinEnum.instFintype _ object.vertices)

@[simp]
theorem mem_vertexFinset (object : FiniteObject) (vertex : object.Vertex) :
    vertex ∈ object.vertexFinset := by
  simp [vertexFinset]

@[simp]
theorem card_vertexFinset (object : FiniteObject) :
    object.vertexFinset.card = object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  simp [vertexFinset, vertexCount, FinEnum.card_eq_fintypeCard]

/-- Neighbours of a vertex, retaining the declared ambient vertex order. -/
def orderedNeighbors (object : FiniteObject) (vertex : object.Vertex) :
    List object.Vertex :=
  object.orderedVertices.filter fun other =>
    @decide (object.graph.Adj vertex other) (object.decideAdj vertex other)

@[simp]
theorem mem_orderedNeighbors_iff (object : FiniteObject)
    (vertex other : object.Vertex) :
    other ∈ object.orderedNeighbors vertex ↔ object.graph.Adj vertex other := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp [orderedNeighbors]

theorem orderedNeighbors_nodup (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.orderedNeighbors vertex).Nodup :=
  object.orderedVertices_nodup.filter _

/-- Darts in lexicographic endpoint order induced by `orderedVertices`. -/
def orderedDarts (object : FiniteObject) : List object.graph.Dart :=
  letI : DecidableRel object.graph.Adj := object.decideAdj
  object.orderedVertices.flatMap fun left =>
    object.orderedVertices.filterMap fun right =>
      if adjacent : object.graph.Adj left right then
        some ⟨(left, right), adjacent⟩
      else
        none

@[simp]
theorem mem_orderedDarts (object : FiniteObject)
    (dart : object.graph.Dart) : dart ∈ object.orderedDarts := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [orderedDarts, List.mem_flatMap]
  refine ⟨dart.fst, object.mem_orderedVertices dart.fst, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨dart.snd, object.mem_orderedVertices dart.snd, ?_⟩
  simp only [dart.adj, ↓reduceDIte]

/-- Edges in first-occurrence order of their two oriented darts. -/
def orderedEdges (object : FiniteObject) : List object.graph.edgeSet := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedDarts.map fun dart =>
    (⟨dart.edge, dart.edge_mem⟩ : object.graph.edgeSet)).dedup

@[simp]
theorem mem_orderedEdges (object : FiniteObject)
    (edge : object.graph.edgeSet) : edge ∈ object.orderedEdges := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [orderedEdges, List.mem_dedup, List.mem_map]
  rcases edge with ⟨edge, edgeMember⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      let dart : object.graph.Dart :=
        ⟨(left, right), edgeMember⟩
      refine ⟨dart, object.mem_orderedDarts dart, ?_⟩
      apply Subtype.ext
      rfl

theorem orderedEdges_nodup (object : FiniteObject) :
    object.orderedEdges.Nodup := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact List.nodup_dedup _

/-- Degree computed by Mathlib from the object's finite data. -/
def degree (object : FiniteObject) (vertex : object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.degree vertex

/-- Instance-independent cardinality form of the bundled degree. -/
theorem degree_eq_ncard_neighborSet (object : FiniteObject)
    (vertex : object.Vertex) :
    object.degree vertex = (object.graph.neighborSet vertex).ncard := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold degree
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp]
theorem orderedNeighbors_length (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.orderedNeighbors vertex).length = object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [← List.toFinset_card_of_nodup (object.orderedNeighbors_nodup vertex)]
  change (object.orderedNeighbors vertex).toFinset.card =
    (object.graph.neighborFinset vertex).card
  congr 1
  ext other
  simp [SimpleGraph.mem_neighborFinset]

/-- Minimum degree computed by Mathlib from the object's finite data. -/
def minDegree (object : FiniteObject) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.minDegree

/-- Maximum degree computed by Mathlib from the object's finite data. -/
def maxDegree (object : FiniteObject) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.maxDegree

/-- Number of undirected Mathlib edges. -/
def edgeCount (object : FiniteObject) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.edgeFinset.card

/-- Instance-independent cardinality form of the bundled edge count. -/
theorem edgeCount_eq_ncard_edgeSet (object : FiniteObject) :
    object.edgeCount = object.graph.edgeSet.ncard := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold edgeCount
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp]
theorem orderedEdges_length (object : FiniteObject) :
    object.orderedEdges.length = object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [← List.toFinset_card_of_nodup object.orderedEdges_nodup]
  calc
    object.orderedEdges.toFinset.card =
        (Finset.univ : Finset object.graph.edgeSet).card := by
      congr 1
      ext edge
      simp
    _ = Fintype.card object.graph.edgeSet := Finset.card_univ
    _ = object.graph.edgeFinset.card := object.graph.card_edgeSet
    _ = object.edgeCount := rfl

theorem minDegree_le_degree (object : FiniteObject)
    (vertex : object.Vertex) :
    object.minDegree ≤ object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.minDegree_le_degree vertex

/-- Prove a lower bound on the bundled minimum degree from pointwise degree
lower bounds. -/
theorem le_minDegree_of_forall_le_degree (object : FiniteObject)
    [nonempty : Nonempty object.Vertex]
    (threshold : Nat)
    (degreeLower : ∀ vertex : object.Vertex,
      threshold ≤ object.degree vertex) :
    threshold ≤ object.minDegree := by
  letI : Nonempty object.Vertex := nonempty
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change threshold ≤ object.graph.minDegree
  apply object.graph.le_minDegree_of_forall_le_degree threshold
  intro vertex
  exact degreeLower vertex

theorem degree_le_maxDegree (object : FiniteObject)
    (vertex : object.Vertex) :
    object.degree vertex ≤ object.maxDegree := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.degree_le_maxDegree vertex

theorem degree_lt_vertexCount (object : FiniteObject)
    (vertex : object.Vertex) :
    object.degree vertex < object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simpa [degree, vertexCount, FinEnum.card_eq_fintypeCard] using
    object.graph.degree_lt_card_verts vertex

theorem edgeCount_le_choose_two (object : FiniteObject) :
    object.edgeCount ≤ object.vertexCount.choose 2 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simpa [edgeCount, vertexCount, FinEnum.card_eq_fintypeCard] using
    (SimpleGraph.card_edgeFinset_le_card_choose_two (G := object.graph))

end FiniteObject

end Hypostructure.Graph
