import Erdos64EG.P13SequentialWeightedHotColdLedger
import StructuralExhaustion.Core.ExactHandoff
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
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 5)
    extends Core.ExactHandoff (p13SequentialWeightedLedger ctx node21) where
  below : P13Route8BelowThreshold ctx
  theta_lt : p13PackingTheta ctx < (1 : ℚ) / 78
  denominatorPositive : 0 < 1 - 13 * p13PackingTheta ctx
  tau_lt : p13Route8Tau (p13PackingTheta ctx) < (3 : ℚ) / 13

/-- No payload on the existing edge `[146] -> [148]`. -/
structure P13Node146To148
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 5)
    extends Core.ExactHandoff (p13SequentialWeightedLedger ctx node21) where
  notBelow : ¬P13Route8BelowThreshold ctx
  crossMultiplied : ctx.G.object.input.vertices.card ≤ 78 * p13 ctx
  theta_ge : (1 : ℚ) / 78 ≤ p13PackingTheta ctx

/-- The two constructors are exactly the two outgoing edges of node `[146]`. -/
inductive P13Node146Outcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 5)
  | to147 : P13Node146To147 ctx node21 → P13Node146Outcome ctx node21
  | to148 : P13Node146To148 ctx node21 → P13Node146Outcome ctx node21

/-- Execute node `[146]` by one natural-number comparison. -/
noncomputable def runP13Node146
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node146Outcome ctx node21 := by
  let previous := p13SequentialWeightedLedger ctx node21
  by_cases below : P13Route8BelowThreshold ctx
  · exact .to147 {
      previous := previous
      previousExact := rfl
      below := below
      theta_lt := (p13Route8BelowThreshold_iff_theta ctx).mp below
      denominatorPositive := p13Route8_denominator_pos_of_below below
      tau_lt := (p13Route8Tau_lt_three_thirteenths_iff
        (p13PackingTheta ctx)
        (p13Route8_denominator_pos_of_below below)).2
          ((p13Route8BelowThreshold_iff_theta ctx).mp below)
    }
  · have crossMultiplied :
        ctx.G.object.input.vertices.card ≤ 78 * p13 ctx := by
      unfold P13Route8BelowThreshold at below
      omega
    exact .to148 {
      previous := previous
      previousExact := rfl
      notBelow := below
      crossMultiplied := crossMultiplied
      theta_ge := le_of_not_gt
        (fun thetaLt => below ((p13Route8BelowThreshold_iff_theta ctx).mpr thetaLt))
    }

/-- Exhaustiveness of the literal yes/no decision. -/
theorem runP13Node146_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (∃ payload, runP13Node146 ctx node21 = .to147 payload) ∨
      (∃ payload, runP13Node146 ctx node21 = .to148 payload) := by
  cases runP13Node146 ctx node21 with
  | to147 payload => exact Or.inl ⟨payload, rfl⟩
  | to148 payload => exact Or.inr ⟨payload, rfl⟩

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
