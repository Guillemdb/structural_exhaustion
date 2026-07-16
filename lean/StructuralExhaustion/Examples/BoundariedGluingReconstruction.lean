import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Examples.BoundariedGluingReconstruction

open StructuralExhaustion.Graph.PackedBoundariedGluing

noncomputable section

/-!
# A non-Erdős reconstruction fixture

The boundary and each side have one vertex.  Both local graphs contain their
single boundary--internal edge, so their literal gluing is a three-vertex
path.  The fixture pins the public ownership API without using any target or
minimal-counterexample semantics.
-/

private def piece : Piece (Fin 1) where
  Internal := Fin 1
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := Classical.decRel _

private def outside : Context (Fin 1) where
  Internal := Fin 1
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := Classical.decRel _
  noBoundaryEdge := by
    intro left right adjacent
    have : left = right := Subsingleton.elim left right
    subst right
    exact adjacent rfl

private def ambient : SimpleGraph
    (Fin 1 ⊕ (piece.Internal ⊕ outside.Internal)) :=
  glueGraph piece outside

/-- The ownership interface reconstructs the concrete three-vertex path. -/
def reconstruction : glueGraph piece outside ≃g ambient :=
  glueGraphIsoOfOwnedPartition piece outside ambient (Equiv.refl _) (by
    intro left right adjacent
    change (glueGraph piece outside).Adj
      (pieceEmbedding piece outside left)
      (pieceEmbedding piece outside right)
    exact (glueGraph_adj_iff piece outside _ _).2
      (Or.inl ⟨left, right, adjacent, rfl, rfl⟩)) (by
    intro left right adjacent
    change (glueGraph piece outside).Adj
      (contextEmbedding piece outside left)
      (contextEmbedding piece outside right)
    exact (glueGraph_adj_iff piece outside _ _).2
      (Or.inr ⟨left, right, adjacent, rfl, rfl⟩)) (by
    intro left right adjacent
    exact (glueGraph_adj_iff piece outside left right).1 adjacent)

example :
    (glueGraph piece outside).Adj (.inl 0)
      (.inr (.inl (0 : Fin 1))) := by
  rw [glueGraph_adj_iff]
  exact Or.inl ⟨.inl 0, .inr (0 : Fin 1), by simp [piece], rfl, rfl⟩

end

end StructuralExhaustion.Examples.BoundariedGluingReconstruction
