import StructuralExhaustion.Graph.FiniteTwoBoundaryPiece
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

open StructuralExhaustion
open PackedBoundariedGluing

universe u

variable {V : Type u} {object : FiniteObject V}

namespace Input

/-- Universe-lifted two-boundary label type used by packed gluing. -/
abbrev LiftedBoundary := ULift.{u} (Fin 2)

def liftedVertexEquiv (input : Input object) :
    LiftedBoundary ⊕ input.Internal ≃ Fin 2 ⊕ input.Internal :=
  Equiv.sumCongr Equiv.ulift (Equiv.refl _)

/-- Regard the literal induced two-boundary input as the standard packed
boundaried piece.  This is a change of API, not a graph search: the internal
type and enumeration are reused, while boundary labels are universe-lifted
through an explicit graph equivalence. -/
def toBoundariedPiece (input : Input object) :
    PackedBoundariedGluing.Piece LiftedBoundary where
  Internal := input.Internal
  internalVertices := input.internalVertices
  graph := SimpleGraph.comap input.liftedVertexEquiv input.piece.graph
  decideAdj := by
    letI : DecidableRel input.piece.graph.Adj := input.piece.decideAdj
    infer_instance

@[simp] theorem toBoundariedPiece_adj_iff (input : Input object)
    (left right : LiftedBoundary ⊕ input.Internal) :
    input.toBoundariedPiece.graph.Adj left right ↔
      input.piece.graph.Adj (input.liftedVertexEquiv left)
        (input.liftedVertexEquiv right) := Iff.rfl

end Input

end StructuralExhaustion.Graph.FiniteTwoBoundaryPiece
