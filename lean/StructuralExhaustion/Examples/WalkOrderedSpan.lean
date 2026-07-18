import StructuralExhaustion.Graph.WalkOrderedSpan

namespace StructuralExhaustion.Examples.WalkOrderedSpan

open StructuralExhaustion
open StructuralExhaustion.Graph

def graph : SimpleGraph (Fin 4) := ⊤

def line : FiniteObject (Fin 4) where
  graph := graph
  input := {
    vertices := inferInstance
    decideAdj := by dsimp [graph]; infer_instance
  }

def path23 : line.graph.Walk 2 3 :=
  .cons (by simp [line, graph]) .nil

def path13 : line.graph.Walk 1 3 :=
  .cons (by simp [line, graph]) path23

def path : line.graph.Walk 0 3 :=
  .cons (by simp [line, graph]) path13

theorem path_isPath : path.IsPath := by native_decide

example : (Graph.WalkOrderedSpan.twoBoundaryInput path path_isPath 1 3
    (by omega) (by native_decide)).support.card ≤ 3 :=
  Graph.WalkOrderedSpan.twoBoundaryInput_card_le_span_add_one
    path path_isPath 1 3 (by omega) (by native_decide)

end StructuralExhaustion.Examples.WalkOrderedSpan
