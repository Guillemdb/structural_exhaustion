import Erdos64EG.Future.P13WeightedColdRestrictedPrefixStages

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- Literal positive earlier prefix positions.  Stage zero does not define a
two-distinct-boundary piece, so it is omitted from the F2/F3 schedule. -/
noncomputable def priorStages (stage : package.Stage) : List package.Stage :=
  (package.stages.values.take stage.val).filter
    fun prior => decide (0 < prior.val)

theorem priorStages_mem_stages_take (stage prior : package.Stage)
    (member : prior ∈ package.priorStages stage) :
    prior ∈ package.stages.values.take stage.val :=
  (List.mem_filter.mp member).1

theorem priorStages_mem_positive (stage prior : package.Stage)
    (member : prior ∈ package.priorStages stage) : 0 < prior.val :=
  of_decide_eq_true (List.mem_filter.mp member).2

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
