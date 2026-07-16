import StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation

namespace StructuralExhaustion.Examples.InducedPathComponentD4D7Evaluation

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object)

example :
    (InducedPathComponentD7.coordinates stage componentInput).card ≤
      (SurplusPairResponse.freePairEnumeration stage).card :=
  InducedPathComponentD4D7Evaluation.d7Checks_le_freePairs stage componentInput

example (coordinate : InducedPathComponentD7.Coordinate stage componentInput) :
    coordinate.support stage componentInput ⊆
      InducedPathComponentD4.activeSupport componentInput :=
  coordinate.support_subset_active stage componentInput

end StructuralExhaustion.Examples.InducedPathComponentD4D7Evaluation
