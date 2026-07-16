import Erdos64EG.P13FiniteRemainderEntropy
import StructuralExhaustion.Core.FinitePowerScaleSplit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [50]: exact entropy-scale dichotomy

The manuscript threshold is executed in its denominator-free natural-number
form `n ^ |R| ≤ N_R ^ 10`.  The runner compares these two supplied powers
once.  It does not evaluate real logarithms or enumerate graphs, states,
subsets, contexts, functions, or Boolean assignments.
-/

/-- Core-owned one-comparison profile built from the exact node-[49] count and
the literal ambient and remainder cardinalities. -/
noncomputable def p13EntropyScaleProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    Core.FinitePowerScaleSplit.Profile where
  base := ctx.G.object.input.vertices.card
  supportSize := (p13RemainderVertices ctx).card
  stateCount := p13RemainderStateCount realized
  scale := 10

/-- The two exact outgoing branches of diagram node `[50]`.  Each constructor
retains the same verified node-[49] predecessor. -/
inductive P13Node50EntropyScaleOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    Type (u + 1)
  | high
      (previous : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
      (exactPrevious : previous = node49)
      (bound : ctx.G.object.input.vertices.card ^
          (p13RemainderVertices ctx).card ≤
        p13RemainderStateCount realized ^ 10)
  | low
      (previous : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
      (exactPrevious : previous = node49)
      (strict : p13RemainderStateCount realized ^ 10 <
        ctx.G.object.input.vertices.card ^
          (p13RemainderVertices ctx).card)

/-- Execute node `[50]` from the exact node-[49] proof. -/
noncomputable def runP13Node50EntropyScaleSplit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    P13Node50EntropyScaleOutcome ctx node21 node24 realized node49 := by
  cases (p13EntropyScaleProfile realized).run with
  | upper bound => exact .high node49 rfl bound
  | lower strict => exact .low node49 rfl strict

/-- The node-[50] branch is exhaustive on the two literal powers. -/
theorem p13Node50EntropyScale_exhaustive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card ≤
          p13RemainderStateCount realized ^ 10 ∨
      p13RemainderStateCount realized ^ 10 <
        ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card := by
  simpa [p13EntropyScaleProfile] using
    (p13EntropyScaleProfile realized).exhaustive

/-- Complete node-[50] single-input/single-output contract. -/
structure VerifiedP13Node50EntropyScaleSplit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    Type (u + 1) where
  previous : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized
  exactPrevious : previous = node49
  outcome : P13Node50EntropyScaleOutcome ctx node21 node24 realized node49
  total : ctx.G.object.input.vertices.card ^
        (p13RemainderVertices ctx).card ≤
      p13RemainderStateCount realized ^ 10 ∨
    p13RemainderStateCount realized ^ 10 <
      ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card
  work : (p13EntropyScaleProfile realized).checks = 1

noncomputable def verifiedP13Node50EntropyScaleSplit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    VerifiedP13Node50EntropyScaleSplit ctx node21 node24 realized node49 where
  previous := node49
  exactPrevious := rfl
  outcome := runP13Node50EntropyScaleSplit node49
  total := p13Node50EntropyScale_exhaustive node49
  work := (p13EntropyScaleProfile realized).checks_eq_one

end Erdos64EG.Internal
