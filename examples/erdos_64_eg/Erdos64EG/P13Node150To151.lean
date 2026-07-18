import Erdos64EG.P13Node150ColdMass
import StructuralExhaustion.Core.ExactHandoff
import Erdos64EG.P13NearCubicSpineHandoff
import Erdos64EG.P13WeightedColdBranchExcess

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing connector `[150] -> [151]`

Node `[151]` consumes the literal cold family produced by node `[150]` and
the near-cubic surplus payment already carried by node `[21]`.  This file
packages that handoff without reconstructing a different cold list and without
adding an outcome to the diagram.
-/

structure P13Node151AmbientCubicColdHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21)
    (node148 : P13Node148To150 ctx node21 node146No)
    (node150 : P13Node150FiniteColdMass ctx node21 node146No node148) :
    Type (u + 4) extends Core.ExactHandoff node150 where
  spine : P13NearCubicSpineBound ctx node21.previous.windowSize
    node21.previous.remainderSize node21.previous.primitiveSize
  coldWindows : List (P13SequentialWeightedColdWindow ctx node21)
  coldWindowsExact : coldWindows = p13SequentialWeightedColdWindows ctx node21
  coldCountExact : coldWindows.length = node150.coldCount
  nearCubicPayment : P13WeightedColdNearCubicPayment ctx node21
  ambientCubicWindows : List (P13WeightedColdCubicWindow ctx node21)
  ambientCubicWindowsExact : ambientCubicWindows =
    p13WeightedColdCubicWindows (ctx := ctx) (node21 := node21)
  nonCubicLossExact : nearCubicPayment.loss =
    (p13WeightedColdNonCubicWindows (ctx := ctx) (node21 := node21)).length

noncomputable def p13Node150To151
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    {node148 : P13Node148To150 ctx node21 node146No}
    (node150 : P13Node150FiniteColdMass ctx node21 node146No node148) :
    P13Node151AmbientCubicColdHandoff ctx node21 node146No node148 node150 := by
  let payment := verifiedP13WeightedColdNearCubicPayment
    (ctx := ctx) (node21 := node21)
  refine {
    previous := node150
    previousExact := rfl
    spine := P13NearCubicSpineBound.ofBoundedSurplus node21.previous
    coldWindows := p13SequentialWeightedColdWindows ctx node21
    coldWindowsExact := rfl
    coldCountExact := ?_
    nearCubicPayment := payment
    ambientCubicWindows :=
      p13WeightedColdCubicWindows (ctx := ctx) (node21 := node21)
    ambientCubicWindowsExact := rfl
    nonCubicLossExact := payment.loss_exact
  }
  rw [node150.coldCountExact]
  rfl

namespace P13Node151AmbientCubicColdHandoff

/-- Exact finite `all but o(n)` statement retained on the immediate
node-`[151]` output. -/
theorem nonCubicLoss_sq_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    {node148 : P13Node148To150 ctx node21 node146No}
    {node150 : P13Node150FiniteColdMass ctx node21 node146No node148}
    (handoff : P13Node151AmbientCubicColdHandoff
      ctx node21 node146No node148 node150) :
    handoff.nearCubicPayment.loss ^ 2 ≤
      surplusScaleCoefficient node21.previous.windowSize
          node21.previous.remainderSize node21.previous.primitiveSize *
        ctx.G.object.input.vertices.card :=
  handoff.nearCubicPayment.loss_sq_le

/-- The node-`[151]` output retains node-`[150]`'s exact cold count. -/
theorem cubic_add_nonCubic_eq_coldCount
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    {node148 : P13Node148To150 ctx node21 node146No}
    {node150 : P13Node150FiniteColdMass ctx node21 node146No node148}
    (handoff : P13Node151AmbientCubicColdHandoff
      ctx node21 node146No node148 node150) :
    handoff.ambientCubicWindows.length + handoff.nearCubicPayment.loss =
      node150.coldCount := by
  rw [handoff.ambientCubicWindowsExact, handoff.nonCubicLossExact,
    ← handoff.coldCountExact, handoff.coldWindowsExact]
  exact p13WeightedCold_cubic_nonCubic_length
    (ctx := ctx) (node21 := node21)

end P13Node151AmbientCubicColdHandoff

end Erdos64EG.Internal
