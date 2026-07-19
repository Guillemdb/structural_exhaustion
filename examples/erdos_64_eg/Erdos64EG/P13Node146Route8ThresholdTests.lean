import Erdos64EG.P13Node146Route8Threshold

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable
  (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
  (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)

example :
    P13Route8BelowThreshold ctx ↔ p13PackingTheta ctx < (1 : ℚ) / 78 :=
  p13Route8BelowThreshold_iff_theta ctx

example (below : P13Route8BelowThreshold ctx) :
    p13Route8Tau (p13PackingTheta ctx) < (3 : ℚ) / 13 := by
  exact (p13Route8Tau_lt_three_thirteenths_iff
    (p13PackingTheta ctx) (p13Route8_denominator_pos_of_below below)).2
      ((p13Route8BelowThreshold_iff_theta ctx).mp below)

example : p13Node146LocalCheckCount ctx ≤
    (ctx.G.object.input.vertices.card + 1) ^ 1 :=
  p13Node146LocalCheckCount_polynomial ctx

example : (p13Node146WorkBudget ctx).checks () = 1 := by
  rfl

#print axioms p13Route8BelowThreshold_iff_theta
#print axioms p13Route8Tau_lt_three_thirteenths_iff
#print axioms p13Node146AccumulatedRun
#print axioms p13Node146LocalCheckCount_polynomial
#print axioms p13Node146WorkBudget_checks

end Erdos64EG.Internal
