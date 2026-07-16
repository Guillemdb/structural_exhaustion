import StructuralExhaustion.Examples.OrderedBFSTree
import StructuralExhaustion.Graph.CubicStarDecomposition

namespace StructuralExhaustion.Examples.CubicStarDecompositionBranch

open StructuralExhaustion

abbrev object := OrderedBFSTreeBranch.object
abbrev star := OrderedBFSTreeBranch.cubicStar

noncomputable def decompositionIso :=
  Graph.CubicStarDecomposition.reconstruction object star

example :
    (Graph.CubicStarDecomposition.piece object star).InternalBaseline
      (inferInstance : FinEnum Graph.CubicStarDecomposition.Boundary) 3 :=
  Graph.CubicStarDecomposition.piece_internalBaseline object star

example : (Graph.CubicStarDecomposition.piece object star).graph.Preconnected :=
  Graph.CubicStarDecomposition.piece_preconnected object star

example (left right : Graph.CubicStarDecomposition.Boundary) :
    ¬(Graph.CubicStarDecomposition.outside object star).graph.Adj
      (.inl left) (.inl right) :=
  Graph.CubicStarDecomposition.boundary_not_owned_by_context object star left right

example (left right : Graph.CubicStarDecomposition.Boundary) :
    (Graph.CubicStarDecomposition.piece object star).graph.Adj
        (.inl left) (.inl right) ↔
      object.graph.Adj
        (Graph.CubicStarDecomposition.boundaryVertex object star left)
        (Graph.CubicStarDecomposition.boundaryVertex object star right) :=
  Graph.CubicStarDecomposition.boundary_owned_by_piece object star left right

example : Graph.CubicStarDecomposition.vertexEquiv object star
    (.inr (.inl ⟨()⟩)) = 2 :=
  rfl

example : Graph.CubicStarDecomposition.constructionChecks object = 20 := by
  native_decide

example : Graph.CubicStarDecomposition.constructionChecks object ≤
    4 * object.input.vertices.card :=
  Graph.CubicStarDecomposition.constructionChecks_linear object

end StructuralExhaustion.Examples.CubicStarDecompositionBranch
