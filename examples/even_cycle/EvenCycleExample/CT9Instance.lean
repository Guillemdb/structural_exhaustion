import EvenCycleExample.CT6Instance

namespace EvenCycleExample

open StructuralExhaustion

universe u

variable {V : Type u}

/-! Public names for the graph layer's generated CT6→CT9 parity route. -/

abbrev endpointRank (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).endpointRank object baseline

abbrev ct9ParityProfile (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct9ParityProfile object baseline

abbrev ct9Capability (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct9Capability object baseline

abbrev endpointNeighborItems (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).endpointNeighborItems object baseline

abbrev ct6ToCT9ItemAdapter (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct6ToCT9ItemAdapter object baseline

abbrev ct9Input (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct9Input object baseline

theorem ct9_three_le_item_cardinality (object : Graph.FiniteObject V)
    (baseline : Baseline object) :
    3 ≤ (ct9Input object baseline).items.values.length :=
  (endpointParityProfile V).ct9_three_le_item_cardinality object baseline

abbrev ct9Run (object : Graph.FiniteObject V) (baseline : Baseline object) :=
  (endpointParityProfile V).ct9Run object baseline

abbrev SameParityEndpointPositions {object : Graph.FiniteObject V}
    {root : V} (path : Graph.RootedPath object.graph root) :=
  Graph.EndpointParityCycle.SameParityEndpointPositions path

abbrev sameParityEndpointPositions (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).sameParityEndpointPositions object baseline

end EvenCycleExample
