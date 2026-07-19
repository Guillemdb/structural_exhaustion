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

/-! ## Manuscript node `[51]` over the constrained family `𝒢(R)` -/

/-- Exact high-branch output of manuscript node `[51]`.

This is the paper-faithful node: it consumes the high edge of the current
node `[50]` dichotomy for the constrained graph family `𝒢(R)`, not the older
conditional finite-state experiment retained below for downstream support. -/
structure VerifiedP13Node51ManuscriptHighEntropyBits
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (node48 : VerifiedP13Node48FrontierCost residual branch node47)
    (node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48)
    (node50 : VerifiedP13Node50ManuscriptEntropySplit
      residual branch node47 node48 node49) :
    Type (u + 5) where
  high : P13Node50High node50
  totalLogBudget :
    ((p13RemainderVertices residual.ctx).card : ℝ) *
        ((1 / 10 : ℝ) *
          Real.logb 2 residual.ctx.G.object.input.vertices.card) ≤
      Real.logb 2 (p13RemainderGraphFamilyCount residual)
  remainderBits :
    (((p13RemainderVertices residual.ctx).card : ℝ) / 10) *
        Real.logb 2 residual.ctx.G.object.input.vertices.card ≤
      Real.logb 2 (p13RemainderGraphFamilyCount residual)
  checks : (p13ManuscriptEntropySplitProfile residual).workBudget.checks () = 0

/-- Construct manuscript node `[51]` from the literal high edge of node `[50]`.
The proof is symbolic arithmetic over the exact node `[49]` entropy identity. -/
noncomputable def verifiedP13Node51ManuscriptHighEntropyBits
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    {node48 : VerifiedP13Node48FrontierCost residual branch node47}
    {node49 : VerifiedP13Node49ManuscriptEntropy residual branch node47 node48}
    (node50 : VerifiedP13Node50ManuscriptEntropySplit
      residual branch node47 node48 node49)
    (high : P13Node50High node50) :
    VerifiedP13Node51ManuscriptHighEntropyBits
      residual branch node47 node48 node49 node50 := by
  let cardR : ℝ := (p13RemainderVertices residual.ctx).card
  let logN : ℝ := Real.logb 2 residual.ctx.G.object.input.vertices.card
  let logG : ℝ := Real.logb 2 (p13RemainderGraphFamilyCount residual)
  have highExpanded :
      (1 / 10 : ℝ) * logN ≤ logG / cardR := by
    simpa [P13Node50High, p13ManuscriptEntropyThreshold,
      p13ManuscriptRemainderEntropy, p13RemainderGraphFamilyCount,
      p13RemainderGraphFamilyProfile, cardR, logN, logG, node49.entropyExact]
      using high
  have cardR_nonneg : 0 ≤ cardR := by
    simp [cardR]
  have totalBudget : cardR * ((1 / 10 : ℝ) * logN) ≤ logG := by
    by_cases hcard : cardR = 0
    ·
      have logG_nonneg : 0 ≤ logG := by
        by_cases hcount : p13RemainderGraphFamilyCount residual = 0
        · simp [logG, hcount]
        · have hcount_pos :
              1 ≤ p13RemainderGraphFamilyCount residual :=
            Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcount)
          have hcount_real :
              (1 : ℝ) ≤ (p13RemainderGraphFamilyCount residual : ℝ) := by
            exact_mod_cast hcount_pos
          exact Real.logb_nonneg (by norm_num) hcount_real
      simpa [hcard] using logG_nonneg
    · have hcard_pos : 0 < cardR := lt_of_le_of_ne' cardR_nonneg hcard
      have scaled := mul_le_mul_of_nonneg_left highExpanded cardR_nonneg
      have div_cancel : cardR * (logG / cardR) = logG := by
        field_simp [hcard]
      nlinarith
  exact {
    high := high
    totalLogBudget := by
      simpa [cardR, logN, logG] using totalBudget
    remainderBits := by
      have h :
          (((p13RemainderVertices residual.ctx).card : ℝ) / 10) *
              Real.logb 2 residual.ctx.G.object.input.vertices.card =
            ((p13RemainderVertices residual.ctx).card : ℝ) *
              ((1 / 10 : ℝ) *
                Real.logb 2 residual.ctx.G.object.input.vertices.card) := by
        ring
      simpa [h] using totalBudget
    checks := node50.work
  }

/-- Ledger-native node `[51]` output.  The framework retains the node `[50]`
decision and its selected high proof; this payload adds only the bit bound. -/
structure P13Node51Output
    (residual : P13Node24RefinementResidual.{u}) : Type (u + 4) where
  totalLogBudget :
    ((p13RemainderVertices residual.ctx).card : ℝ) *
        ((1 / 10 : ℝ) *
          Real.logb 2 residual.ctx.G.object.input.vertices.card) ≤
      Real.logb 2 (p13RemainderGraphFamilyCount residual)
  remainderBits :
    (((p13RemainderVertices residual.ctx).card : ℝ) / 10) *
        Real.logb 2 residual.ctx.G.object.input.vertices.card ≤
      Real.logb 2 (p13RemainderGraphFamilyCount residual)
  checks : (p13ManuscriptEntropySplitProfile residual).workBudget.checks () = 0

noncomputable def p13Node51Output
    {residual : P13Node24RefinementResidual.{u}}
    (node50 : P13Node50Output residual)
    (high : P13Node50OutputHigh residual node50) : P13Node51Output residual := by
  let cardR : ℝ := (p13RemainderVertices residual.ctx).card
  let logN : ℝ := Real.logb 2 residual.ctx.G.object.input.vertices.card
  let logG : ℝ := Real.logb 2 (p13RemainderGraphFamilyCount residual)
  have highExpanded : (1 / 10 : ℝ) * logN ≤
      logG / cardR := by
    simpa [P13Node50OutputHigh, p13ManuscriptEntropyThreshold,
      p13ManuscriptRemainderEntropy, p13RemainderGraphFamilyCount,
      p13RemainderGraphFamilyProfile, cardR, logN, logG] using high
  have cardR_nonneg : 0 ≤ cardR := by simp [cardR]
  have totalBudget : cardR * ((1 / 10 : ℝ) * logN) ≤ logG := by
    by_cases hcard : cardR = 0
    · have logG_nonneg : 0 ≤ logG := by
        by_cases hcount : p13RemainderGraphFamilyCount residual = 0
        · simp [logG, hcount]
        · have hcount_pos : 1 ≤ p13RemainderGraphFamilyCount residual :=
            Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcount)
          have hcount_real : (1 : ℝ) ≤
              (p13RemainderGraphFamilyCount residual : ℝ) := by
            exact_mod_cast hcount_pos
          exact Real.logb_nonneg (by norm_num) hcount_real
      simpa [hcard] using logG_nonneg
    · have hcard_pos : 0 < cardR := lt_of_le_of_ne' cardR_nonneg hcard
      have scaled := mul_le_mul_of_nonneg_left highExpanded cardR_nonneg
      have divCancel : cardR * (logG / cardR) = logG := by field_simp [hcard]
      nlinarith
  exact {
    totalLogBudget := by simpa [cardR, logN, logG] using totalBudget
    remainderBits := by
      calc
        (((p13RemainderVertices residual.ctx).card : ℝ) / 10) *
            Real.logb 2 residual.ctx.G.object.input.vertices.card =
          cardR * ((1 / 10 : ℝ) * logN) := by
            simp [cardR, logN]; ring
        _ ≤ logG := totalBudget
        _ = Real.logb 2 (p13RemainderGraphFamilyCount residual) := rfl
    checks := node50.work
  }

/-! ## Retained conditional support for the earlier finite-state route -/

/-- Exact high-branch output of node `[51]`. -/
structure VerifiedP13Node51HighEntropyBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) : Type (u + 6)
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
      ctx node21 node24 realized node49) : Type (u + 6)
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
