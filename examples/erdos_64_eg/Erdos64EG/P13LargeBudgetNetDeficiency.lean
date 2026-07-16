import Erdos64EG.P13DensityConnectedRankPrefix
import StructuralExhaustion.Core.FiniteBudgetTransfer

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact finite handoff to the Part-IV net-deficiency cap

This file isolates the arithmetic available after node `[24]` has supplied an
exact packing ceiling on the same selected graph as the node-`[21]` curvature
table and the node-`[47]` rank ledger.  It does not construct that ceiling and
does not claim the still-missing entropy or spine theorem.

The single additional predicate is the cross-multiplied finite budget needed
for a strict quarter cap.  It uses the predecessor's packing ceiling and its
induced remainder floor, so no division or asymptotic error is hidden here.
-/

/-- Exact natural-number numerator of the remainder net deficiency. -/
noncomputable def p13NetDeficiencyNumerator
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  (p13RemainderCurvatureProfile ctx).positiveDeficiency -
    Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object

/-- Largest surplus-adjusted numerator justified by the supplied packing
ceiling and the existing window-incidence ledger. -/
noncomputable def p13CoverageNetBudgetUpper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) : Nat :=
  15 * coverage.windowCeiling +
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
    Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object

/-- Exact finite predicate owed by the upstream window/spine budget. -/
def P13QuarterNetBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) : Prop :=
  4 * p13CoverageNetBudgetUpper ctx (node21 := node21) coverage <
    coverage.remainderFloor

/-- The incidence supply and genuine node-`[24]` packing ceiling bound the
actual net numerator by the exact budget above. -/
theorem p13NetDeficiencyNumerator_le_coverageBudget
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage) :
    p13NetDeficiencyNumerator ctx ≤
      p13CoverageNetBudgetUpper ctx (node21 := node21) coverage := by
  have supply := joined.globalRank.previous.previous.surplusAdjustedSupply
  have packingBound :
      15 * p13 ctx +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
        15 * coverage.windowCeiling +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 15 coverage.packing_le) _
  exact supply.trans (Nat.sub_le_sub_right packingBound _)

/-- Conditional but exact node-`[56]` arithmetic in cross-multiplied form. -/
theorem p13NetDeficiency_strict_quarter
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (budget : P13QuarterNetBudget ctx (node21 := node21) coverage) :
    4 * p13NetDeficiencyNumerator ctx < (p13RemainderVertices ctx).card := by
  exact Core.FiniteBudgetTransfer.strict_scaled_of_le_of_lt_of_le
    (p13NetDeficiencyNumerator_le_coverageBudget joined)
    budget joined.remainder.large

/-- Expanded statement matching the manuscript numerator literally. -/
theorem p13NetDeficiency_strict_quarter_explicit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (budget : P13QuarterNetBudget ctx (node21 := node21) coverage) :
    4 * ((p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object) <
      (p13RemainderVertices ctx).card := by
  simpa [p13NetDeficiencyNumerator] using
    p13NetDeficiency_strict_quarter joined budget

/-- Honest typed handoff retaining the exact predecessor, the externally owed
finite budget proof, and its strict-quarter consequence. -/
structure P13QuarterNetDeficiencyHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) where
  previous : P13DensityConnectedGlobalRankPrefix ctx node21 coverage
  budget : P13QuarterNetBudget ctx (node21 := node21) coverage
  strictQuarter :
    4 * p13NetDeficiencyNumerator ctx < (p13RemainderVertices ctx).card

/-- Construct the handoff only from the same-context prefix and the declared
exact finite budget predicate. -/
def p13QuarterNetDeficiencyHandoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (budget : P13QuarterNetBudget ctx (node21 := node21) coverage) :
    P13QuarterNetDeficiencyHandoff ctx node21 coverage where
  previous := joined
  budget := budget
  strictQuarter := p13NetDeficiency_strict_quarter joined budget

end Erdos64EG.Internal
