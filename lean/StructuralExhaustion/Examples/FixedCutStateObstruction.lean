import StructuralExhaustion.Core.FixedCutStateObstruction

namespace StructuralExhaustion.Examples.FixedCutStateObstruction

open Core.FixedCutStateObstruction

/-! A non-Erdős execution of both fixed-state obstruction theorems. -/

example :
    100 < Fintype.card (RawTwoInterface (Fin 101)) := by
  exact rawTwoInterface_exceeds 100

example : ∃ state : RawConnectorLength,
    1000 < state.connectorLength :=
  rawConnectorLength_exceeds 1000

example : ∃ state : RawD1D2State (Fin 3),
    1000 < state.connectorLength :=
  rawD1D2_exceeds (Fin 3) (0, 1) 1000

end StructuralExhaustion.Examples.FixedCutStateObstruction
