import Erdos64EG.P13EntropyScaleSplit
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [51]: high-power remainder bit contribution

This node consumes only node `[50]`'s actual high constructor and derives the
paper's total-bit inequality.  It neither divides by the remainder size nor
asserts the joint window/remainder accounting still owed at node `[52]`.
-/

/-- Exact high-branch output of node `[51]`. -/
structure VerifiedP13Node51HighEntropyBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) : Type (u + 1)
    extends Core.ExactHandoff node50 where
  powerBound : ctx.G.object.input.vertices.card ^
      (p13RemainderVertices ctx).card ≤
    p13RemainderStateCount realized ^ 10
  totalLogBudget :
    ((p13RemainderVertices ctx).card : ℝ) *
        Real.logb 2 ctx.G.object.input.vertices.card ≤
      (10 : ℝ) * Real.logb 2 (p13RemainderStateCount realized)
  remainderBits :
    (((p13RemainderVertices ctx).card : ℝ) / 10) *
        Real.logb 2 ctx.G.object.input.vertices.card ≤
      Real.logb 2 (p13RemainderStateCount realized)
  checks : (p13EntropyScaleProfile realized).checks = 1

/-- Construct node `[51]` only when the supplied node-[50] contract's actual
outcome is its high constructor.  The equality prevents attaching a freshly
restated power bound to an unrelated split. -/
noncomputable def verifiedP13Node51HighEntropyBits
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (outcomePrevious : VerifiedP13Node49FiniteEntropy
      ctx node21 node24 realized)
    (outcomeExactPrevious : outcomePrevious = node49)
    (bound : ctx.G.object.input.vertices.card ^
        (p13RemainderVertices ctx).card ≤
      p13RemainderStateCount realized ^ 10)
    (actualHigh : node50.outcome =
      .high outcomePrevious outcomeExactPrevious bound) :
    VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50 := by
  let totalBudget :
      ((p13RemainderVertices ctx).card : ℝ) *
          Real.logb 2 ctx.G.object.input.vertices.card ≤
        (10 : ℝ) * Real.logb 2 (p13RemainderStateCount realized) := by
    simpa [p13EntropyScaleProfile] using
      (p13EntropyScaleProfile realized).logb_budget_of_upper
        node49.countPos bound
  exact {
    previous := node50
    previousExact := rfl
    powerBound := bound
    totalLogBudget := totalBudget
    remainderBits := by
      nlinarith [totalBudget]
    checks := node50.work
  }

/-- Compatibility spelling; exact handoff storage is framework-owned. -/
theorem VerifiedP13Node51HighEntropyBits.exactPrevious
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) :
    node51.previous = node50 :=
  node51.previousExact

/-- Total routing at the node-[50] branch point: the actual high constructor
produces node `[51]`, while the strict low constructor is retained unchanged
for its separate node-[53] consumer. -/
inductive P13Node50To51Route
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) : Type (u + 1)
  | high
      (output : VerifiedP13Node51HighEntropyBits
        ctx node21 node24 realized node49 node50)
  | low
      (previous : VerifiedP13Node50EntropyScaleSplit
        ctx node21 node24 realized node49)
      (exactPrevious : previous = node50)
      (outcomePrevious : VerifiedP13Node49FiniteEntropy
        ctx node21 node24 realized)
      (outcomeExactPrevious : outcomePrevious = node49)
      (strict : p13RemainderStateCount realized ^ 10 <
        ctx.G.object.input.vertices.card ^
          (p13RemainderVertices ctx).card)
      (actualLow : node50.outcome =
        .low outcomePrevious outcomeExactPrevious strict)

noncomputable def routeP13Node50To51
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) :
    P13Node50To51Route ctx node21 node24 realized node49 node50 := by
  cases outcomeEq : node50.outcome with
  | high previous exactPrevious bound =>
      exact .high (verifiedP13Node51HighEntropyBits
        node50 previous exactPrevious bound outcomeEq)
  | low previous exactPrevious strict =>
      exact .low node50 rfl previous exactPrevious strict outcomeEq

end Erdos64EG.Internal
