import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Fixtures.GraphContraction
import Hypostructure.Fixtures.GraphOneThreeRepair
import Hypostructure.Graph.Theorems

/-!
# Reusable graph theorem profiles fixture

This fixture exercises three independent reusable graph theorem profiles with
no EG-specific constants.
-/

namespace Hypostructure.Fixtures.GraphTheorems

open Hypostructure.Fixtures.GraphBasics
open Hypostructure.Graph.Theorems

theorem cycleTargetExample :
    Hypostructure.Graph.HasCycleWithLength (fun length => length = 4) c4 :=
  c4_has_four_cycle

theorem contractionExample :
    (Hypostructure.Graph.contractionFiniteObject GraphContraction.bridgeGraph
        (0 : Fin 2) (1 : Fin 2)).vertexCount <
      GraphContraction.bridgeGraph.vertexCount := by
  exact GraphContraction.contracted_vertexCount_lt

theorem oneThreeRepairExample :
    (GraphOneThreeRepair.component.internal.card : Int) =
      GraphOneThreeRepair.component.boundary.card - 2 +
        2 * GraphOneThreeRepair.component.cycleRank -
        GraphOneThreeRepair.component.surplus := by
  exact GraphOneThreeRepair.repair_identity

end Hypostructure.Fixtures.GraphTheorems
