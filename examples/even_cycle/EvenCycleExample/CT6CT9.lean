import EvenCycleExample.CT9Instance

namespace EvenCycleExample

open StructuralExhaustion

universe u

variable {V : Type u}

/-! Public names for the graph layer's generated chord-cycle conclusion. -/

abbrev evenCycleCertificate (object : Graph.FiniteObject V)
    (baseline : Baseline object) :=
  (endpointParityProfile V).evenCycleCertificate object baseline

theorem hasEvenCycle_of_minDegree_three (object : Graph.FiniteObject V)
    (baseline : Baseline object) : HasEvenCycle object :=
  (endpointParityProfile V).target_of_baseline object baseline

end EvenCycleExample
