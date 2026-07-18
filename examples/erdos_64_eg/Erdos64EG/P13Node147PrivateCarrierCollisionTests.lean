import Erdos64EG.P13Node147PrivateCarrierCollision

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  (node146 : P13Node146To147 ctx node21)

example : p13Route8Tau (p13PackingTheta ctx) <
    12 * ((1 : ℚ) / 4 - p13Route8Tau (p13PackingTheta ctx)) :=
  p13Route8CollisionCoefficientGap node146

example : 0 < 3 - 13 * p13Route8Tau (p13PackingTheta ctx) :=
  p13Route8CollisionMargin_pos node146

example : (p13Node147ArithmeticPrefix node146).previous = node146 := rfl

example : p13Node147ArithmeticCheckCount
      (p13Node147ArithmeticPrefix node146) ≤
    (ctx.G.object.input.vertices.card + 1) ^ 1 :=
  p13Node147ArithmeticCheckCount_polynomial _

#print axioms p13Route8CollisionCoefficientGap
#print axioms p13Route8CollisionMargin_pos
#print axioms p13Node147ArithmeticCheckCount_polynomial

end Erdos64EG.Internal
