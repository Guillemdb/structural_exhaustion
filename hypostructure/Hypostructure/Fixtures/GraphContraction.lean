import Hypostructure.Graph.Contraction

/-!
# Graph contraction fixture

This fixture exercises the contraction primitive on a one-edge finite graph.
-/

namespace Hypostructure.Fixtures.GraphContraction

open Hypostructure.Graph

def bridgeGraph : FiniteObject where
  Vertex := Fin 2
  graph := SimpleGraph.fromEdgeSet {s((0 : Fin 2), (1 : Fin 2))}
  vertices := inferInstance
  decideAdj := inferInstance

def contracted : FiniteObject :=
  contractionFiniteObject bridgeGraph (0 : Fin 2) (1 : Fin 2)

theorem contracted_vertexCount_lt :
    contracted.vertexCount < bridgeGraph.vertexCount := by
  simpa [contracted] using
    (vertexCount_lt bridgeGraph (0 : Fin 2) (1 : Fin 2))

end Hypostructure.Fixtures.GraphContraction
