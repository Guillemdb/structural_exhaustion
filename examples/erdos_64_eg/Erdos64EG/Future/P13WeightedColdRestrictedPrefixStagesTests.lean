import Erdos64EG.Future.P13WeightedColdRestrictedPrefixStages

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

example : package.stages.values.Nodup := package.stages_nodup

example (stage : package.Stage) :
    (package.prefixSupport stage).Nodup ∧ package.prefixSupport stage ≠ [] :=
  ⟨package.prefixSupport_nodup stage,
    package.prefixSupport_nonempty stage⟩

example {earlier later : package.Stage} (ordered : earlier.val ≤ later.val) :
    package.prefixSupport earlier <+: package.prefixSupport later :=
  package.prefixSupport_prefix ordered

example :
    package.checks ≤
      (InducedPathRestrictedComponentBoundarySchedule.componentObject
        package.input).input.vertices.card :=
  package.checks_le_componentCarrier

end Erdos64EG.Internal
