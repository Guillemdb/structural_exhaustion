import Erdos64EG.P13WeightedColdComponentEntries

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

example :
    (p13WeightedColdComponentEntries
      (ctx := ctx) (node21 := node21)).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length :=
  p13WeightedColdComponentEntries_length

example (entry : P13WeightedColdComponentEntry ctx node21) :
    (∃ boundary boundaryExact input inputExact,
      entry.route = .component boundary boundaryExact input inputExact) ∨
    (∃ residual, entry.route = .crossWindow residual) :=
  entry.route_exhaustive

example :
    (p13WeightedColdComponentEntriesWithTag
      (ctx := ctx) (node21 := node21) .component).length +
      (p13WeightedColdComponentEntriesWithTag
        (ctx := ctx) (node21 := node21) .crossWindow).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length :=
  p13WeightedColdComponentEntries_partition

example :
    p13WeightedColdComponentEntryChecks
      (ctx := ctx) (node21 := node21) ≤
      ctx.G.object.input.vertices.card :=
  p13WeightedColdComponentEntryChecks_linear

end Erdos64EG.Internal
