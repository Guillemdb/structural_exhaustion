import EvenCycleExample.Problem

namespace EvenCycleExample

open StructuralExhaustion

universe u

variable {V : Type u}

/-! Public names for the graph layer's generated CT6 endpoint-path API. -/

abbrev chosenMaximalPath (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).chosenMaximalPath object baseline

abbrev branchContext (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).branchContext object baseline

abbrev ct6Spec (V : Type u) := (endpointParityProfile V).ct6Spec

abbrev ct6Capability (object : Graph.FiniteObject V) :=
  (endpointParityProfile V).ct6Capability object

theorem ct6_no_failure (object : Graph.FiniteObject V)
    (baseline : Baseline object) (vertex : V) :
    ¬(ct6Spec V).Failure (branchContext object baseline) vertex :=
  (endpointParityProfile V).ct6_no_failure object baseline vertex

abbrev ct6Run (object : Graph.FiniteObject V) (baseline : Baseline object) :=
  (endpointParityProfile V).ct6Run object baseline

theorem ct6_endpoint_closed (object : Graph.FiniteObject V)
    (baseline : Baseline object) :
    ∀ vertex,
      object.graph.Adj
        (chosenMaximalPath object baseline).2.path.endpoint vertex →
      vertex ∈ (chosenMaximalPath object baseline).2.path.vertices :=
  (endpointParityProfile V).ct6_endpoint_closed object baseline

end EvenCycleExample
