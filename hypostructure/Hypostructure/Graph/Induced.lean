import Hypostructure.Graph.Finite

/-!
# Finite induced restrictions

Restriction uses `SimpleGraph.induce` on the subtype of an explicit finite
support.  The subtype schedule is derived from the incoming object's schedule.
-/

namespace Hypostructure.Graph

namespace FiniteObject

/-- Restrict a packed finite graph to an explicit finite vertex support. -/
def induce (object : FiniteObject) (support : Finset object.Vertex) :
    FiniteObject where
  Vertex := {vertex : object.Vertex // vertex ∈ support}
  graph := object.graph.induce (support : Set object.Vertex)
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidablePred (fun vertex : object.Vertex => vertex ∈ support) :=
      fun vertex => @Finset.decidableMem object.Vertex object.vertices.decEq
        vertex support
    infer_instance
  decideAdj := by
    letI : DecidableRel object.graph.Adj := object.decideAdj
    infer_instance

/-- Canonical embedding of an induced restriction into its source graph. -/
def induceEmbedding (object : FiniteObject)
    (support : Finset object.Vertex) :
    (object.induce support).graph ↪g object.graph :=
  SimpleGraph.Embedding.induce (support : Set object.Vertex)

@[simp]
theorem induceEmbedding_apply (object : FiniteObject)
    (support : Finset object.Vertex)
    (vertex : (object.induce support).Vertex) :
    object.induceEmbedding support vertex = vertex.1 :=
  rfl

@[simp]
theorem vertexCount_induce (object : FiniteObject)
    (support : Finset object.Vertex) :
    (object.induce support).vertexCount = support.card := by
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  rw [vertexCount, FinEnum.card_eq_fintypeCard]
  calc
    @Fintype.card induced.Vertex
        (@FinEnum.instFintype induced.Vertex induced.vertices) =
        @Fintype.card {vertex : object.Vertex // vertex ∈ support}
          (Finset.Subtype.fintype support) :=
      @Fintype.card_congr' induced.Vertex
        {vertex : object.Vertex // vertex ∈ support}
        (@FinEnum.instFintype induced.Vertex induced.vertices)
        (Finset.Subtype.fintype support) rfl
    _ = support.card := Fintype.card_coe support

theorem induce_le (object : FiniteObject)
    (support : Finset object.Vertex) :
    (object.induce support).graph.map
        (object.induceEmbedding support).toEmbedding ≤ object.graph := by
  exact SimpleGraph.map_comap_le _ _

theorem degree_induce_of_neighborSet_subset
    (object : FiniteObject) (support : Finset object.Vertex)
    (vertex : (object.induce support).Vertex)
    (closed : object.graph.neighborSet vertex.1 ⊆ (support : Set object.Vertex)) :
    (object.induce support).degree vertex = object.degree vertex.1 := by
  rw [degree]
  rw [degree]
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  letI : DecidableRel induced.graph.Adj := induced.decideAdj
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr
    { toFun := fun neighbor => ⟨neighbor.1.1, neighbor.2⟩
      invFun := fun neighbor =>
        ⟨⟨neighbor.1, closed neighbor.2⟩, neighbor.2⟩
      left_inv := fun neighbor => by ext; rfl
      right_inv := fun neighbor => by ext; rfl }

end FiniteObject

end Hypostructure.Graph
