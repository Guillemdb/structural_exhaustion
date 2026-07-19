import Erdos64EG.P13HighEntropyRemainderBits
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.FinitePoweredBudgetTransfer

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [53]: exact low-entropy forced-cost fit

This node consumes the actual strict-low constructor of node `[50]`.  The
node-`[48]` conditional-fibre ledger bounds the forced curvature power by the
flat power times the exact node-`[49]` state count.  Node `[50]` then makes the
same comparison strict after raising to scale ten.  Thus the printed
small-budget edge is impossible on this branch, while the surviving
large-budget edge remains conditional on the separate quarter-budget producer
required by node `[55]`.
-/

/-- Proof-carrying input for the literal low constructor of node `[50]`.
The outcome equality prevents a caller from restating the strict inequality
independently of the verified split. -/
structure P13Node53LowEntropyInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) : Type (u + 1)
    extends Core.ExactHandoff node50 where
  outcomePrevious : VerifiedP13Node49FiniteEntropy
    ctx node21 node24 realized
  outcomeExactPrevious : outcomePrevious = node49
  strict : p13RemainderStateCount realized ^ 10 <
    ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card
  actualLow : node50.outcome =
    .low outcomePrevious outcomeExactPrevious strict

/-- Extract node `[53]`'s input only from the already executed node-[50] route. -/
def P13Node50To51Route.lowInput
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (previous : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (exactPrevious : previous = node50)
    (outcomePrevious : VerifiedP13Node49FiniteEntropy
      ctx node21 node24 realized)
    (outcomeExactPrevious : outcomePrevious = node49)
    (strict : p13RemainderStateCount realized ^ 10 <
      ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card)
    (actualLow : node50.outcome =
      .low outcomePrevious outcomeExactPrevious strict) :
    P13Node53LowEntropyInput ctx node21 node24 realized node49 node50 where
  previous := previous
  previousExact := exactPrevious
  outcomePrevious := outcomePrevious
  outcomeExactPrevious := outcomeExactPrevious
  strict := strict
  actualLow := actualLow

/-- Exact forced curvature power from the node-[48] coordinate schedule. -/
noncomputable def p13Node53ForcedPower
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  543958 ^ (p13CurvatureCoordinates ctx).card

/-- Exact flat comparison power on the same coordinate schedule. -/
noncomputable def p13Node53FlatPower
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  111286 ^ (p13CurvatureCoordinates ctx).card

/-- Node `[53]`'s remaining low-entropy allowance. -/
noncomputable def p13Node53UpperPower
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  ctx.G.object.input.vertices.card ^ (p13RemainderVertices ctx).card

/-- Literal small-budget comparison at scale ten. -/
def P13Node53SmallBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Prop :=
  p13Node53FlatPower ctx ^ 10 * p13Node53UpperPower ctx ≤
    p13Node53ForcedPower ctx ^ 10

/-- The exact node-[48] telescoping ledger bounds forced power by flat power
times the exact supplied state count, without invoking the larger ambient
skeleton capacity. -/
theorem p13Node53_forcedPower_le_flatPower_mul_stateCount
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized) :
    p13Node53ForcedPower ctx ≤
      p13Node53FlatPower ctx * p13RemainderStateCount realized := by
  have terminalOne : 1 ≤ realized.ledger.finalStates.length :=
    realized.finalNonempty
  have lower : p13Node53ForcedPower ctx ≤
      p13Node53ForcedPower ctx * realized.ledger.finalStates.length := by
    simpa using Nat.mul_le_mul_left (p13Node53ForcedPower ctx) terminalOne
  have telescoped := realized.ledger.power_product_le
  calc
    p13Node53ForcedPower ctx ≤
        p13Node53ForcedPower ctx * realized.ledger.finalStates.length := lower
    _ ≤ p13Node53FlatPower ctx * realized.states.values.length := by
      simpa [p13Node53ForcedPower, p13Node53FlatPower,
        FinEnum.toOrderedCollection_length] using telescoped
    _ = p13Node53FlatPower ctx * p13RemainderStateCount realized := by
      rw [node49.stateCountExact]

/-- Core-owned symbolic powered-budget transfer instantiated on the exact
node-[48]/[49]/[50] values. -/
noncomputable def p13Node53PoweredBudgetProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (input : P13Node53LowEntropyInput
      ctx node21 node24 realized node49 node50) :
    Core.FinitePoweredBudgetTransfer.Profile where
  forced := p13Node53ForcedPower ctx
  flat := p13Node53FlatPower ctx
  stateCount := p13RemainderStateCount realized
  upper := p13Node53UpperPower ctx
  scale := 10
  forced_le_flat_mul_stateCount :=
    p13Node53_forcedPower_le_flatPower_mul_stateCount node49
  stateCount_pow_lt_upper := input.strict
  flat_pos := by
    exact Nat.pow_pos (by norm_num)

/-- Complete node-[53] output.  It proves the strict reverse of the printed
small-budget test and exposes only a conditional node-[55] consumer. -/
structure VerifiedP13Node53LargeBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (input : P13Node53LowEntropyInput
      ctx node21 node24 realized node49 node50) : Type (u + 1)
    extends Core.ExactHandoff input where
  strictLarge : p13Node53ForcedPower ctx ^ 10 <
    p13Node53FlatPower ctx ^ 10 * p13Node53UpperPower ctx
  notSmall : ¬P13Node53SmallBudget ctx
  consume : P13QuarterNetBudget ctx (node21 := node21) node24.coverage →
    P13QuarterNetDeficiencyHandoff ctx node21 node24.coverage
  checks : (p13Node53PoweredBudgetProfile input).checks = 0

/-- Execute node `[53]` by symbolic inequality transport only. -/
noncomputable def verifiedP13Node53LargeBudget
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (input : P13Node53LowEntropyInput
      ctx node21 node24 realized node49 node50) :
    VerifiedP13Node53LargeBudget
      ctx node21 node24 realized node49 node50 input := by
  let strictLarge := (p13Node53PoweredBudgetProfile input).forced_pow_lt_flat_pow_mul_upper
  exact {
    previous := input
    previousExact := rfl
    strictLarge := strictLarge
    notSmall := Nat.not_le_of_lt strictLarge
    consume := fun budget =>
      p13QuarterNetDeficiencyHandoff node24.globalRankPrefix budget
    checks := (p13Node53PoweredBudgetProfile input).checks_eq_zero
  }

/-- The yes/small edge of node `[53]` is impossible on its exact incoming
strict-low branch. -/
theorem p13Node53_smallBudget_impossible
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    {input : P13Node53LowEntropyInput
      ctx node21 node24 realized node49 node50}
    (output : VerifiedP13Node53LargeBudget
      ctx node21 node24 realized node49 node50 input)
    (small : P13Node53SmallBudget ctx) : False :=
  output.notSmall small

/-- Total branch handoff from the executed node-[50] split.  The high branch
retains node `[51]`; the actual low branch executes node `[53]`. -/
inductive P13Node50BudgetRoute
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) : Type (u + 2)
  | high (output : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50)
  | low
      (input : P13Node53LowEntropyInput
        ctx node21 node24 realized node49 node50)
      (output : VerifiedP13Node53LargeBudget
        ctx node21 node24 realized node49 node50 input)

/-- Execute the exact high/low successors without a fresh branch assumption. -/
noncomputable def routeP13Node50Budget
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) :
    P13Node50BudgetRoute ctx node21 node24 realized node49 node50 := by
  cases routeP13Node50To51 node50 with
  | high output => exact .high output
  | low previous exactPrevious outcomePrevious outcomeExactPrevious strict actualLow =>
      let input : P13Node53LowEntropyInput
          ctx node21 node24 realized node49 node50 := {
        previous := previous
        previousExact := exactPrevious
        outcomePrevious := outcomePrevious
        outcomeExactPrevious := outcomeExactPrevious
        strict := strict
        actualLow := actualLow
      }
      exact .low input (verifiedP13Node53LargeBudget input)

/-- The total handoff exposes exactly one of the two verified successors. -/
theorem routeP13Node50Budget_exhaustive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49) :
    (∃ output, routeP13Node50Budget node50 = .high output) ∨
      (∃ input output, routeP13Node50Budget node50 = .low input output) := by
  cases outcome : routeP13Node50Budget node50 with
  | high output => exact Or.inl ⟨output, rfl⟩
  | low input output => exact Or.inr ⟨input, output, rfl⟩

end Erdos64EG.Internal
