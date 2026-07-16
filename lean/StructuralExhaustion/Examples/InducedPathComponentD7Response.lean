import StructuralExhaustion.Graph.InducedPathComponentD7Response

namespace StructuralExhaustion.Examples.InducedPathComponentD7Response

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)

example :
    (Graph.InducedPathComponentD7Response.responseProfile stage
      componentInput).coordinates =
        Graph.InducedPathComponentD7.coordinates stage componentInput :=
  Graph.InducedPathComponentD7Response.coordinates_exact stage componentInput

example
    (coordinate : Graph.InducedPathComponentD7.Coordinate stage componentInput)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    (Graph.InducedPathComponentD7Response.responseProfile stage
        componentInput).responseSystem.response coordinate outside =
      (Graph.SurplusPairResponse.responseProfile stage).responseSystem.response
        coordinate.1 outside :=
  Graph.InducedPathComponentD7Response.response_eq_sparsePairResponse
    stage componentInput coordinate outside

end StructuralExhaustion.Examples.InducedPathComponentD7Response
