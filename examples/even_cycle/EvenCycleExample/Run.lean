import EvenCycleExample.CT6CT9
import EvenCycleExample.CT1Instance

namespace EvenCycleExample

open StructuralExhaustion

universe u

abbrev finalCT1Input {V : Type u} (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct1Input object baseline

/-- CT1 validates the public certificate produced by the CT6→CT9 route. -/
abbrev finalCT1Run {V : Type u} (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).ct1Run object baseline

/-- A finite Mathlib graph of minimum degree at least three has an even
simple cycle. -/
theorem minimumDegreeThree_hasEvenCycle {V : Type u}
    (object : Graph.FiniteObject V) (baseline : Baseline object) :
    HasEvenCycle object :=
  (endpointParityProfile V).target_of_baseline object baseline

end EvenCycleExample
