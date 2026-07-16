import StructuralExhaustion.Graph.InducedPathComponentD7

namespace StructuralExhaustion.Examples.InducedPathComponentD7

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)

/-! The fixture is target-independent: every emitted D7 coordinate retains
its exact sparse-pair support and a proof that the support is contained in the
stored component interface. -/

example (coordinate :
    Graph.InducedPathComponentD7.Coordinate stage componentInput) :
    coordinate.support stage componentInput ⊆
      Graph.InducedPathComponentD4.activeSupport componentInput :=
  coordinate.support_subset_active stage componentInput

example :
    (Graph.InducedPathComponentD7.coordinates stage componentInput).card ≤
      (Graph.SurplusPairResponse.freePairEnumeration stage).card :=
  Graph.InducedPathComponentD7.coordinates_card_le_freePairs
    stage componentInput

end StructuralExhaustion.Examples.InducedPathComponentD7
