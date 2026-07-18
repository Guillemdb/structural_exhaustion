import StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

namespace StructuralExhaustion.Examples.FiniteTwoBoundaryPiece

open StructuralExhaustion

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject Vertex where
  graph := graph
  input := {
    vertices := inferInstance
    decideAdj := by
      dsimp [graph]
      infer_instance
  }

def support : Finset Vertex := {0, 1, 2}

def input : Graph.FiniteTwoBoundaryPiece.Input object where
  support := support
  left := 0
  right := 2
  left_mem := by simp [support]
  right_mem := by simp [support]
  left_ne_right := by decide

example : input.vertexEquiv (.inl 0) = ⟨0, input.left_mem⟩ := rfl

example : input.vertexEquiv (.inl 1) = ⟨2, input.right_mem⟩ := rfl

example : input.vertexEquiv (.inr ⟨1, by simp [input, support]⟩) =
    ⟨1, by simp [input, support]⟩ := rfl

example : input.piece.graph.Adj (.inl 0)
    (.inr ⟨1, by simp [input, support]⟩) := by
  rw [input.boundary_adj_iff]
  change object.graph.Adj 0 1
  simp [object, graph]

example :
    input.piece.boundaryDegree 0 = 2 := by
  rw [input.boundaryDegree_eq_supportedNeighbors]
  native_decide

example : Set.range (fun vertex : Fin 2 ⊕ input.Internal =>
    (input.vertexEquiv vertex).1) = (input.support : Set Vertex) :=
  input.vertex_image_eq_support

end StructuralExhaustion.Examples.FiniteTwoBoundaryPiece
