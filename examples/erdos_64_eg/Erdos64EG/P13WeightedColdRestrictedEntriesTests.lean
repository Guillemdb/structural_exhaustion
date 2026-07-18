import Erdos64EG.P13WeightedColdRestrictedEntries

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

example (entry : P13WeightedColdRestrictedEntry ctx node21) :
    (∃ boundary tokenExact,
      entry.route = .componentBoundary boundary tokenExact) ∨
    (∃ residual, entry.route = .crossWindow residual) :=
  entry.route_exhaustive

example :
    (p13WeightedColdRestrictedEntriesWithTag
      (ctx := ctx) (node21 := node21) .componentBoundary).length +
      (p13WeightedColdRestrictedEntriesWithTag
        (ctx := ctx) (node21 := node21) .crossWindow).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length :=
  p13WeightedColdRestrictedEntries_partition

example :
    p13WeightedColdRestrictedEntryChecks
      (ctx := ctx) (node21 := node21) ≤
      ctx.G.object.input.vertices.card :=
  p13WeightedColdRestrictedEntryChecks_linear

end Erdos64EG.Internal

