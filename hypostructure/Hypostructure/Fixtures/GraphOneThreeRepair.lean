import Mathlib.Combinatorics.SimpleGraph.Star
import Hypostructure.Graph.OneThreeRepair

/-!
# One-three Graph fixture

The four-vertex star supplies one internal degree-three vertex and three
degree-one boundary vertices.  The fixture exercises the Graph contract and
the Core affine repair without any theorem-specific target data.
-/

namespace Hypostructure.Fixtures.GraphOneThreeRepair

open Hypostructure.Graph
open Hypostructure.Graph.OneThreeRepair

abbrev star4 : FiniteObject where
  Vertex := Fin 4
  graph := SimpleGraph.starGraph 0
  vertices := inferInstance
  decideAdj := inferInstance

def boundary : Finset star4.Vertex := {1, 2, 3}

def component : Component where
  object := star4
  boundary := boundary
  boundaryDegree := by
    intro vertex member
    have ne : vertex ≠ 0 := by
      fin_cases vertex <;> simp_all [boundary]
    change (SimpleGraph.starGraph (0 : Fin 4)).degree vertex = 1
    exact SimpleGraph.degree_starGraph_of_ne_center ne
  internalDegreeThree := by
    intro vertex notBoundary
    fin_cases vertex
    · change 3 ≤ (SimpleGraph.starGraph (0 : Fin 4)).degree 0
      rw [SimpleGraph.degree_starGraph_center]
      decide
    all_goals
      exfalso
      apply notBoundary
      simp [boundary]
  boundaryCard_le_edgeCount := by
    decide
  connected := by
    exact SimpleGraph.connected_starGraph 0

theorem repair_identity :
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank -
        component.surplus :=
  component.identity

#print axioms repair_identity

end Hypostructure.Fixtures.GraphOneThreeRepair
