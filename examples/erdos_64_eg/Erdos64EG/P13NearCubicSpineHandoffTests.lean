import Erdos64EG.P13NearCubicSpineHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

example (bounded : BoundedSurplusScaleResidual ctx) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient bounded.windowSize bounded.remainderSize
          bounded.primitiveSize * ctx.G.object.input.vertices.card :=
  (P13NearCubicSpineBound.ofBoundedSurplus bounded).surplus_sq_le

example (windowSize remainderSize primitiveSize : Nat)
    (within : (coupledClassProfile ctx windowSize remainderSize primitiveSize
      ).WithinCapacity (coupledClassItems ctx)) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card :=
  (P13NearCubicSpineBound.ofNoCoupledOverload ctx windowSize remainderSize
    primitiveSize within).surplus_sq_le

#print axioms P13NearCubicSpineBound.ofBoundedSurplus
#print axioms P13NearCubicSpineBound.ofNoCoupledOverload
#print axioms P13Node144NearCubicHandoff.surplus_sq_le

end Erdos64EG.Internal
