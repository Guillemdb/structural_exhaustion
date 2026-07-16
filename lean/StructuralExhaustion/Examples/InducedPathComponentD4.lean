import StructuralExhaustion.Graph.InducedPathComponentD4

namespace StructuralExhaustion.Examples.InducedPathComponentD4

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}

/-! Non-Erdos transfer of the graph-owned D4 family on one supplied component input. -/

theorem d4_is_local_and_cubic
    (input : InducedPathComponentBoundarySchedule.Input object) :
    InducedPathComponentD4.visibleChecks input ≤
      4 * object.input.vertices.card ^ 3 :=
  InducedPathComponentD4.visibleChecks_le_cubic input

theorem every_d4_coordinate_has_a_literal_wedge
    (input : InducedPathComponentBoundarySchedule.Input object)
    (coordinate : InducedPathComponentD4.Coordinate input) :
    object.graph.Adj coordinate.2.center coordinate.2.left ∧
      object.graph.Adj coordinate.2.center coordinate.2.right ∧
      coordinate.2.left ≠ coordinate.2.right :=
  ⟨coordinate.2.adjacent_left, coordinate.2.adjacent_right,
    coordinate.2.left_ne_right⟩

end StructuralExhaustion.Examples.InducedPathComponentD4
