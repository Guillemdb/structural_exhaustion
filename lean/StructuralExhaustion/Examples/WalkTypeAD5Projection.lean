import StructuralExhaustion.Graph.WalkTypeAD5Projection

namespace StructuralExhaustion.Examples.WalkTypeAD5Projection

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {left right : ctx.G.Vertex}
variable (walk : ctx.G.object.graph.Walk left right)

/-- The local degree decision exposes exactly the D6 handoff or the cubic
Type-A input; no graph or support universe is enumerated. -/
example (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) :
    (∃ high, WalkTypeAD5Projection.degreeSplit walk minimumDegreeThree =
        .high high) ∨
      (∃ cubic, WalkTypeAD5Projection.degreeSplit walk minimumDegreeThree =
        .noHigh cubic) := by
  cases equation : WalkTypeAD5Projection.degreeSplit walk minimumDegreeThree with
  | high high => exact Or.inl ⟨high, rfl⟩
  | noHigh cubic => exact Or.inr ⟨cubic, rfl⟩

example (profile : TypeACanonicalReceiverTrace.SupportProfile ctx.G.object)
    (coordinate : WalkTypeAD5Projection.Profile.Coordinate profile) :
    coordinate ∈
      (WalkTypeAD5Projection.Profile.coordinates profile).orderedValues :=
  WalkTypeAD5Projection.Profile.coordinate_mem profile coordinate

end StructuralExhaustion.Examples.WalkTypeAD5Projection
