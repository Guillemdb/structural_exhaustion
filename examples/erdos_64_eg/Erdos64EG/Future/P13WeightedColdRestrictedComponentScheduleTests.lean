import Erdos64EG.Future.P13WeightedColdRestrictedComponentSchedule

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

example :
    (p13WeightedColdRestrictedComponentSchedule
      (ctx := ctx) (node21 := node21)).length =
      (p13WeightedColdRestrictedEntries
        (ctx := ctx) (node21 := node21)).length :=
  p13WeightedColdRestrictedComponentSchedule_length

end Erdos64EG.Internal

