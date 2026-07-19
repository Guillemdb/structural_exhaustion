import Erdos64EG.P13SequentialWeightedHotColdLedger
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Core.WorkBudget

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [146]: the exact route-8 density threshold

This file consumes the canonical packing-order ledger of node `[145]` and
performs the single arithmetic decision displayed at node `[146]`.  The
decision is the denominator-free comparison `78 * p13 < n`; no graph,
context, state family, or ambient universe is enumerated.
-/

/-- The manuscript density `theta = p13 / n`, represented exactly in `Rat`. -/
noncomputable def p13PackingTheta
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ℚ :=
  (p13 ctx : ℚ) / ctx.G.object.input.vertices.card

/-- The manuscript's normalized route-8 load
`tau(theta) = 15 theta / (1 - 13 theta)`. -/
def p13Route8Tau (theta : ℚ) : ℚ :=
  15 * theta / (1 - 13 * theta)

/-- The exact executable predicate at node `[146]`.  Cross multiplication
avoids rational division in the decision procedure. -/
noncomputable def P13Route8BelowThreshold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop :=
  78 * p13 ctx < ctx.G.object.input.vertices.card

noncomputable instance p13Route8BelowThresholdDecidable
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Decidable (P13Route8BelowThreshold ctx) := by
  unfold P13Route8BelowThreshold
  infer_instance

/-- The minimal-counterexample graph has positive order.  This uses only the
already established minimum-degree-three baseline, not a later diagram node. -/
theorem p13VertexCount_pos
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    0 < ctx.G.object.input.vertices.card := by
  have baseline := (packedStaticInput.fixedContext ctx).baseline
  change 3 ≤ ctx.G.object.minDegree at baseline
  letI : Nonempty ctx.G.Vertex :=
    ctx.G.object.nonempty_of_minDegree_pos (by omega)
  let vertex : ctx.G.Vertex := Classical.choice inferInstance
  exact Nat.zero_lt_of_lt (ctx.G.object.degree_lt_vertexCount vertex)

/-- The cross-multiplied executable test is exactly `theta < 1/78`. -/
theorem p13Route8BelowThreshold_iff_theta
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    P13Route8BelowThreshold ctx ↔ p13PackingTheta ctx < (1 : ℚ) / 78 := by
  have nposNat := p13VertexCount_pos ctx
  have npos : (0 : ℚ) < ctx.G.object.input.vertices.card := by
    exact_mod_cast nposNat
  unfold P13Route8BelowThreshold p13PackingTheta
  constructor <;> intro h
  · apply (div_lt_iff₀ npos).2
    have hq : (78 : ℚ) * p13 ctx <
        ctx.G.object.input.vertices.card := by
      exact_mod_cast h
    norm_num
    linarith
  · have scaled := (div_lt_iff₀ npos).1 h
    have hq : (78 : ℚ) * p13 ctx <
        ctx.G.object.input.vertices.card := by
      norm_num at scaled
      linarith
    exact_mod_cast hq

/-- On the natural domain `13 theta < 1`, the printed route-8 rational
inequality is equivalent to the threshold `theta < 1/78`.  Positivity of the
denominator is explicit, so the theorem does not silently divide by zero. -/
theorem p13Route8Tau_lt_three_thirteenths_iff
    (theta : ℚ) (denominatorPositive : 0 < 1 - 13 * theta) :
    p13Route8Tau theta < (3 : ℚ) / 13 ↔ theta < (1 : ℚ) / 78 := by
  unfold p13Route8Tau
  rw [div_lt_iff₀ denominatorPositive]
  constructor <;> intro h <;> linarith

/-- A successful threshold test automatically puts the actual packing density
inside the positive-denominator domain of `tau`. -/
theorem p13Route8_denominator_pos_of_below
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (below : P13Route8BelowThreshold ctx) :
    0 < 1 - 13 * p13PackingTheta ctx := by
  have thetaLt := (p13Route8BelowThreshold_iff_theta ctx).mp below
  linarith

/-- Yes payload on the existing edge `[146] -> [147]`. -/
structure P13Node146To147
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 5) where
  below : P13Route8BelowThreshold ctx
  theta_lt : p13PackingTheta ctx < (1 : ℚ) / 78
  denominatorPositive : 0 < 1 - 13 * p13PackingTheta ctx
  tau_lt : p13Route8Tau (p13PackingTheta ctx) < (3 : ℚ) / 13

/-- No payload on the existing edge `[146] -> [148]`. -/
structure P13Node146To148
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 5) where
  notBelow : ¬P13Route8BelowThreshold ctx
  crossMultiplied : ctx.G.object.input.vertices.card ≤ 78 * p13 ctx
  theta_ge : (1 : ℚ) / 78 ≤ p13PackingTheta ctx

/-! ## Framework-owned accumulated execution

The stable residual names the graph prefix.  Node `[145]` attaches its
canonical weighted ledger exactly once; every later state retains it by type.
Node `[146]` contributes only the threshold decision and its arithmetic
consequences.
-/

structure P13Node145RefinementResidual where
  ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}
  node21 : VerifiedP13MultiScaleCurvaturePrefix ctx

abbrev P13Node145LedgerStage (residual : P13Node145RefinementResidual.{u}) :=
  P13SequentialWeightedLedger residual.ctx residual.node21

noncomputable def p13Node145LedgerRefinement {facts} :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node145LedgerStage where
  produce := fun state =>
    p13SequentialWeightedLedger state.residual.ctx state.residual.node21

abbrev P13Node146Below (residual : P13Node145RefinementResidual.{u}) : Prop :=
  P13Route8BelowThreshold residual.ctx

abbrev P13Node146NotBelow
    (residual : P13Node145RefinementResidual.{u}) : Prop :=
  ¬P13Route8BelowThreshold residual.ctx

noncomputable def p13Node146DecisionRefinement {facts} :
    Core.ResidualRefinement.State.DecisionNode (facts := facts)
      P13Node146Below P13Node146NotBelow :=
  Core.ResidualRefinement.State.DecisionNode.complement _
    (fun state => p13Route8BelowThresholdDecidable state.residual.ctx)

abbrev P13Node146To147Stage (residual : P13Node145RefinementResidual.{u}) :=
  P13Node146To147 residual.ctx residual.node21

abbrev P13Node146To148Stage (residual : P13Node145RefinementResidual.{u}) :=
  P13Node146To148 residual.ctx residual.node21

noncomputable def p13Node146To147Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node146Below facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node146To147Stage :=
  Core.ResidualRefinement.State.StageNode.usingFact
      (required := P13Node146Below) fun state below =>
    { below := below
      theta_lt := (p13Route8BelowThreshold_iff_theta state.residual.ctx).mp below
      denominatorPositive := p13Route8_denominator_pos_of_below below
      tau_lt := (p13Route8Tau_lt_three_thirteenths_iff
        (p13PackingTheta state.residual.ctx)
        (p13Route8_denominator_pos_of_below below)).2
          ((p13Route8BelowThreshold_iff_theta state.residual.ctx).mp below) }

noncomputable def p13Node146To148Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node146NotBelow facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node146To148Stage :=
  Core.ResidualRefinement.State.StageNode.usingFact
      (required := P13Node146NotBelow) fun state notBelow =>
    { notBelow := notBelow
      crossMultiplied := by
        change ¬(78 * p13 state.residual.ctx <
          state.residual.ctx.G.object.input.vertices.card) at notBelow
        omega
      theta_ge := le_of_not_gt
        (fun thetaLt => notBelow
          ((p13Route8BelowThreshold_iff_theta state.residual.ctx).mpr thetaLt)) }

noncomputable def p13Node145InitialState
    (residual : P13Node145RefinementResidual.{u}) :=
  p13Node145LedgerRefinement.run
    (Core.ResidualRefinement.State.initial residual)

noncomputable def p13Node146AccumulatedRun
    (residual : P13Node145RefinementResidual.{u}) :=
  (p13Node146DecisionRefinement.run (p13Node145InitialState residual)).mapStages
    p13Node146To147Refinement p13Node146To148Refinement

/-- The node performs one primitive arithmetic comparison. -/
def p13Node146LocalCheckCount
    (_ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat := 1

/-- The one-comparison schedule is constant, hence polynomial. -/
theorem p13Node146LocalCheckCount_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node146LocalCheckCount ctx ≤
      (ctx.G.object.input.vertices.card + 1) ^ 1 := by
  simp [p13Node146LocalCheckCount]

/-- Machine-readable constant-work certificate for the exact node `[146]`
comparison. -/
def p13Node146WorkBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.constant
    (fun _ => ctx.G.object.input.vertices.card) 1

@[simp] theorem p13Node146WorkBudget_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13Node146WorkBudget ctx).checks () = p13Node146LocalCheckCount ctx := by
  rfl

end Erdos64EG.Internal
