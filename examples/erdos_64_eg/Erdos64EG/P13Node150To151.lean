import Erdos64EG.P13Node150ColdMass
import StructuralExhaustion.Core.ResidualRefinement
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
    Type (u + 4) where
  spine : P13NearCubicSpineBound ctx node21.previous.windowSize
    node21.previous.remainderSize node21.previous.primitiveSize
  nearCubicPayment : P13WeightedColdNearCubicPayment ctx node21
  cubicPartition :
    (p13WeightedColdCubicWindows (ctx := ctx) (node21 := node21)).length +
        nearCubicPayment.loss = node150.coldCount

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
    spine := P13NearCubicSpineBound.ofBoundedSurplus node21.previous
    nearCubicPayment := payment
    cubicPartition := ?_
  }
  rw [payment.loss_exact, node150.coldCountExact]
  exact p13WeightedCold_cubic_nonCubic_length
    (ctx := ctx) (node21 := node21)

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
    (p13WeightedColdCubicWindows (ctx := ctx) (node21 := node21)).length +
        handoff.nearCubicPayment.loss =
      node150.coldCount := by
  exact handoff.cubicPartition

end P13Node151AmbientCubicColdHandoff

abbrev P13Node151RefinementStage
    (residual : P13Node145RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node150RefinementStage
    (fun residual node150 => P13Node151AmbientCubicColdHandoff residual.ctx
      residual.node21 node150.previous.previous node150.previous.output
        node150.output) residual

noncomputable def p13Node151Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node150RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node151RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node150 => p13Node150To151 node150.output)

end Erdos64EG.Internal
