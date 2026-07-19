import Erdos64EG.P13FiniteRemainderEntropy
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.FinitePowerScaleSplit
import StructuralExhaustion.Core.OrderThresholdSplit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [50]: the manuscript entropy dichotomy

The original diagram asks exactly whether
`η(R) ≥ (1/10) log₂ n`.  This file instantiates the Core-owned proof-level
ordered split on node `[49]`'s symbolic entropy.  It evaluates neither the
logarithm nor the constrained graph family.
-/

/-- The exact threshold printed at node `[50]`. -/
noncomputable def p13ManuscriptEntropyThreshold
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  (1 / 10 : ℝ) * Real.logb 2 residual.ctx.G.object.input.vertices.card

/-- Core-owned ordered split instantiated with node `[49]`'s literal
`η(R)` and the manuscript threshold. -/
noncomputable def p13ManuscriptEntropySplitProfile
    (residual : P13Node24RefinementResidual.{u}) :
    Core.OrderThresholdSplit.Profile ℝ where
  value := p13ManuscriptRemainderEntropy residual
  threshold := p13ManuscriptEntropyThreshold residual

/-- Node `[50]` retains the exact node-`[49]` value and adds only the
framework-owned exhaustive threshold outcome. -/
structure VerifiedP13Node50ManuscriptEntropySplit
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (node48 : VerifiedP13Node48FrontierCost residual branch node47)
    (node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48) :
    Type (u + 5) where
  outcome : (p13ManuscriptEntropySplitProfile residual).Outcome
  total : p13ManuscriptEntropyThreshold residual ≤
      p13ManuscriptRemainderEntropy residual ∨
    p13ManuscriptRemainderEntropy residual <
      p13ManuscriptEntropyThreshold residual
  work : (p13ManuscriptEntropySplitProfile residual).workBudget.checks () = 0

/-- Execute the original node `[50]` dichotomy from the exact node-`[49]`
predecessor, preserving the complete dependent residual through
`Core.ExactHandoff`. -/
noncomputable def VerifiedP13Node49ManuscriptEntropy.node50
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    {node48 : VerifiedP13Node48FrontierCost residual branch node47}
    (node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48) :
    VerifiedP13Node50ManuscriptEntropySplit residual branch node47 node48 node49 where
  outcome := (p13ManuscriptEntropySplitProfile residual).run
  total := (p13ManuscriptEntropySplitProfile residual).exhaustive
  work := (p13ManuscriptEntropySplitProfile residual).checks_eq_zero

/-- The exact yes-edge proposition of the original diagram. -/
def P13Node50High
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    {node48 : VerifiedP13Node48FrontierCost residual branch node47}
    {node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48}
    (node50 : VerifiedP13Node50ManuscriptEntropySplit
      residual branch node47 node48 node49) : Prop :=
  p13ManuscriptEntropyThreshold residual ≤
    p13ManuscriptRemainderEntropy residual

/-- The exact no-edge proposition of the original diagram. -/
def P13Node50Low
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    {node48 : VerifiedP13Node48FrontierCost residual branch node47}
    {node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48}
    (node50 : VerifiedP13Node50ManuscriptEntropySplit
      residual branch node47 node48 node49) : Prop :=
  p13ManuscriptRemainderEntropy residual <
    p13ManuscriptEntropyThreshold residual

theorem VerifiedP13Node50ManuscriptEntropySplit.high_or_low
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    {node48 : VerifiedP13Node48FrontierCost residual branch node47}
    {node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48}
    (node50 : VerifiedP13Node50ManuscriptEntropySplit
      residual branch node47 node48 node49) :
    P13Node50High node50 ∨ P13Node50Low node50 :=
  node50.total

/-- Ledger-native node `[50]` payload.  Node `[49]` remains in the accumulated
stage ledger and is not copied into this output. -/
structure P13Node50Output
    (residual : P13Node24RefinementResidual.{u}) : Type (u + 4) where
  outcome : (p13ManuscriptEntropySplitProfile residual).Outcome
  total : p13ManuscriptEntropyThreshold residual ≤
      p13ManuscriptRemainderEntropy residual ∨
    p13ManuscriptRemainderEntropy residual <
      p13ManuscriptEntropyThreshold residual
  work : (p13ManuscriptEntropySplitProfile residual).workBudget.checks () = 0

noncomputable def p13Node50Output
    (residual : P13Node24RefinementResidual.{u}) : P13Node50Output residual where
  outcome := (p13ManuscriptEntropySplitProfile residual).run
  total := (p13ManuscriptEntropySplitProfile residual).exhaustive
  work := (p13ManuscriptEntropySplitProfile residual).checks_eq_zero

abbrev P13Node50OutputHigh
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50Output residual) : Prop :=
  p13ManuscriptEntropyThreshold residual ≤
    p13ManuscriptRemainderEntropy residual

abbrev P13Node50OutputLow
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50Output residual) : Prop :=
  p13ManuscriptRemainderEntropy residual <
    p13ManuscriptEntropyThreshold residual

/-! ## Retained conditional support for the earlier realized-state route

These declarations are deliberately not evidence for manuscript node `[50]`.
They remain available because later conditional modules still consume that
separate finite-state experiment while they are migrated to `𝒢(R)`.
-/

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

inductive P13Node50EntropyScaleOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    Type (u + 6)
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

structure VerifiedP13Node50EntropyScaleSplit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    Type (u + 6) extends Core.ExactHandoff node49 where
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
  previousExact := rfl
  outcome := runP13Node50EntropyScaleSplit node49
  total := p13Node50EntropyScale_exhaustive node49
  work := (p13EntropyScaleProfile realized).checks_eq_one

theorem VerifiedP13Node50EntropyScaleSplit.exactPrevious
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) :
    node50.previous = node49 :=
  node50.previousExact

end Erdos64EG.Internal
