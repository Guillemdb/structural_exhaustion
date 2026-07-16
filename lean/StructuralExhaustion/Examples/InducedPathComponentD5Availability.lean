import StructuralExhaustion.Graph.InducedPathComponentD5Availability

namespace StructuralExhaustion.Examples.InducedPathComponentD5Availability

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable (componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object)
variable (ownership : InducedPathComponentD5Availability.Ownership componentInput)

example (coordinate : ownership.Coordinate) :
    coordinate.support ctx.G.object ownership.profile ⊆
      InducedPathComponentD4.activeSupport componentInput :=
  ownership.coordinate_support_subset_active componentInput coordinate

example : (ownership.coordinates componentInput).card ≤
    ctx.G.object.input.vertices.card *
      (ctx.G.object.input.vertices.card + 1) :=
  ownership.coordinates_quadratic componentInput

example : InducedPathComponentD5Availability.missingInputs.Nodup :=
  InducedPathComponentD5Availability.missingInputs_nodup

end StructuralExhaustion.Examples.InducedPathComponentD5Availability
