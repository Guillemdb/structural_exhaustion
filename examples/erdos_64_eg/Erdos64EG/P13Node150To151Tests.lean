import Erdos64EG.P13Node150To151

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  {node146No : P13Node146To148 ctx node21}
  {node148 : P13Node148To150 ctx node21 node146No}
  (node150 : P13Node150FiniteColdMass ctx node21 node146No node148)

example : (p13Node150To151 node150).previous = node150 :=
  (p13Node150To151 node150).previousExact

example :
    (p13Node150To151 node150).ambientCubicWindows.length +
        (p13Node150To151 node150).nearCubicPayment.loss = node150.coldCount :=
  (p13Node150To151 node150).cubic_add_nonCubic_eq_coldCount

example : (p13Node150To151 node150).nearCubicPayment.loss ^ 2 ≤
    surplusScaleCoefficient node21.previous.windowSize
        node21.previous.remainderSize node21.previous.primitiveSize *
      ctx.G.object.input.vertices.card :=
  (p13Node150To151 node150).nonCubicLoss_sq_le

#print axioms p13Node150To151
#print axioms P13Node151AmbientCubicColdHandoff.nonCubicLoss_sq_le
#print axioms P13Node151AmbientCubicColdHandoff.cubic_add_nonCubic_eq_coldCount

end Erdos64EG.Internal
