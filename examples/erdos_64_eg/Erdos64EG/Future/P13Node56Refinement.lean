import Erdos64EG.Future.P13Node53Refinement
import Erdos64EG.Future.P13LargeBudgetNetDeficiency
import Erdos64EG.Future.P13ForcedCurvatureCost
import StructuralExhaustion.Core.DensityAsymptoticTransport
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Accumulated manuscript node [56]

Node `[56]` combines three already accumulated inputs on the literal
node-`[55]` branch: node `[24]` supplies the remainder-scaled density cap,
node `[29]` supplies the surplus-adjusted incidence inequality, and node
`[55]` supplies branch provenance. `LedgerQuery` retrieves all three at one
stable residual. The output stores only node `[56]`'s new normalized net-cap
statement.
-/

/-- Exact additive error retained by the finite node-[56] normalization. -/
noncomputable def p13Node56NetError
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  15 * (p13SequentialHotNormalizationError
      residual.ctx residual.node21 : ℝ) /
      ((p13WindowRemainderRateDenominator : ℝ) *
        p13Node48NormalizationScale residual.ctx) +
    Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object

/-- A temporary named view of node `[56]`'s inherited ledger inputs.  It is
consumed during derivation and is not retained in the node output. -/
structure P13Node56Inputs
    (residual : P13Node24RefinementResidual.{u}) : Type (u + 5) where
  density : P13Node24RemainderDensityFact residual
  supply : P13Node29SurplusAdjustedSupplyFact residual
  node55 : P13Node55RefinementStage.{u, u} residual

/-- The sole new mathematical payload of node `[56]`. -/
structure P13Node56Output
    (residual : P13Node24RefinementResidual.{u}) : Type (u + 4) where
  netCap :
    (p13NetDeficiencyNumerator residual.ctx : ℝ) ≤
      p13Node24TauWindow * (p13RemainderVertices residual.ctx).card +
        p13Node56NetError residual
  limitingCapStrict : p13Node24TauWindow < (1 / 4 : ℝ)

/-- Assemble node `[56]`'s named input view from one accumulated state. -/
noncomputable def p13Node56InputsQuery {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node24Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node29Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node55RefinementStage) facts] :
  Core.ResidualRefinement.State.LedgerQuery
      (facts := facts) P13Node56Inputs :=
  (((Core.ResidualRefinement.State.LedgerQuery.entailedStage
      (facts := facts) (Stage := P13Node24Stage)
      (property := P13Node24RemainderDensityFact)).andEntailedStage
      (Stage := P13Node29Stage)
      (property := P13Node29SurplusAdjustedSupplyFact)).andStage
      (Stage := P13Node55RefinementStage)).map fun _residual inputs =>
        ⟨inputs.fst.fst, inputs.fst.snd, inputs.snd⟩

/-- Node `[29]`'s literal supply, weakened only by its own exact surplus
partition.  No incidence ledger is recomputed. -/
theorem p13Node56_supply_from_node29
    {residual : P13Node24RefinementResidual.{u}}
    (supply : P13Node29SurplusAdjustedSupplyFact residual) :
    p13NetDeficiencyNumerator residual.ctx ≤
      15 * p13 residual.ctx +
        Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object := by
  rw [p13,
    ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
  exact supply

/-- The finite error-bearing node `[56]` cap from the three queried
predecessors.  The node-[55] value is used only as exact branch provenance. -/
noncomputable def p13Node56FromInputs
    (residual : P13Node24RefinementResidual.{u})
    (inputs : P13Node56Inputs residual) : P13Node56Output residual := by
  let scale := p13Node48NormalizationScale residual.ctx
  have scalePositive : (0 : ℝ) < scale := by
    exact_mod_cast (p13Node48NormalizationScale_pos residual)
  have ratePositive : (0 : ℝ) < p13WindowRemainderRateDenominator := by
    norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have densityNat :
      p13WindowRemainderRateDenominator * p13 residual.ctx * scale ≤
        p13WindowDensitySkeletonNumerator *
            (p13RemainderVertices residual.ctx).card * scale +
          p13SequentialHotNormalizationError residual.ctx residual.node21 :=
    inputs.density
  have densityReal :
      (p13WindowRemainderRateDenominator : ℝ) * p13 residual.ctx * scale ≤
        (p13WindowDensitySkeletonNumerator : ℝ) *
            (p13RemainderVertices residual.ctx).card * scale +
          p13SequentialHotNormalizationError residual.ctx residual.node21 := by
    exact_mod_cast densityNat
  have supplyReal :
      (p13NetDeficiencyNumerator residual.ctx : ℝ) ≤
        15 * p13 residual.ctx +
          Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object := by
    exact_mod_cast p13Node56_supply_from_node29 inputs.supply
  have cap :=
    Core.DensityAsymptoticTransport.scaled_density_supply_with_error
      ratePositive scalePositive densityReal supplyReal (by norm_num : (0 : ℝ) ≤ 15)
  have tauIdentity :
      (15 : ℝ) * p13WindowDensitySkeletonNumerator /
          p13WindowRemainderRateDenominator = p13Node24TauWindow := by
    norm_num [p13Node24TauWindow, p13Node24ThetaWindow,
      p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have capRewritten :
      (p13NetDeficiencyNumerator residual.ctx : ℝ) ≤
        p13Node24TauWindow * (p13RemainderVertices residual.ctx).card +
          p13Node56NetError residual := by
    rw [tauIdentity] at cap
    simpa [p13Node56NetError, scale, mul_assoc, add_assoc] using cap
  exact {
    netCap := capRewritten
    limitingCapStrict := by
      norm_num [p13Node24TauWindow, p13Node24ThetaWindow,
        p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  }

/-- Framework-owned node `[56]` derivation from an arbitrary accumulated
branch ledger containing the three declared inputs. -/
noncomputable def p13Node56Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node24Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node29Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node55RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) P13Node56Output :=
  Core.ResidualRefinement.State.StageNode.derive p13Node56InputsQuery
    fun state inputs => p13Node56FromInputs state.residual inputs

/-- Continue only the exact large-budget leaf of the accumulated Part-IV
run. -/
noncomputable def p13Nodes25To56Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To55Run residual).mapNoStage p13Node56Refinement

theorem p13Nodes25To56Run_retains_residual
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To56Run residual with
    | .yesBranch branch => branch.state.residual = residual
    | .noBranch branch => branch.state.residual = residual := by
  unfold p13Nodes25To56Run
  cases p13Nodes25To55Run residual with
  | yesBranch branch => exact branch.residualExact
  | noBranch branch => exact branch.residualExact

/-- Ledger retrieval and normalization add no graph scan. -/
def p13Node56LocalChecks : Nat := 0

theorem p13Node56LocalChecks_eq_zero : p13Node56LocalChecks = 0 := rfl

/-! ## The explicit error is genuinely `o(|R|)` -/

theorem p13Node56NetError_nonnegative
    (residual : P13Node24RefinementResidual.{u}) :
    0 ≤ p13Node56NetError residual := by
  unfold p13Node56NetError
  positivity

/-- The node-[56] error is bounded by the already framework-normalized
near-cubic envelope.  This is coefficient arithmetic only; no predecessor
fact or graph ledger is recomputed. -/
theorem p13Node56NetError_le_node48RankError
    (residual : P13Node24RefinementResidual.{u}) :
    p13Node56NetError residual ≤ p13Node48RankError residual := by
  let normalization : ℝ :=
    (p13SequentialHotNormalizationError
      residual.ctx residual.node21 : ℝ) /
      p13Node48NormalizationScale residual.ctx
  let surplus : ℝ :=
    Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object
  have normalizationNonnegative : 0 ≤ normalization := by
    dsimp [normalization]
    positivity
  have surplusNonnegative : 0 ≤ surplus := by
    dsimp [surplus]
    positivity
  have normalizationCoefficient :
      (15 : ℝ) / p13WindowRemainderRateDenominator ≤ 30 := by
    norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have surplusCoefficient :
      (1 : ℝ) ≤ 2 * p13WindowRemainderRateDenominator := by
    norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have normalizationBound := mul_le_mul_of_nonneg_right
    normalizationCoefficient normalizationNonnegative
  have surplusBound := mul_le_mul_of_nonneg_right
    surplusCoefficient surplusNonnegative
  have normalizationIdentity :
      15 * (p13SequentialHotNormalizationError
          residual.ctx residual.node21 : ℝ) /
          ((p13WindowRemainderRateDenominator : ℝ) *
            p13Node48NormalizationScale residual.ctx) =
        ((15 : ℝ) / p13WindowRemainderRateDenominator) * normalization := by
    dsimp [normalization]
    ring
  have rankNormalizationIdentity :
      30 * (p13SequentialHotNormalizationError
          residual.ctx residual.node21 : ℝ) /
          p13Node48NormalizationScale residual.ctx = 30 * normalization := by
    dsimp [normalization]
    ring
  rw [p13Node56NetError, p13Node48RankError, normalizationIdentity]
  rw [rankNormalizationIdentity]
  simpa [normalization, surplus, mul_assoc] using
    add_le_add normalizationBound surplusBound

/-- Uniform fixed-threshold family form of the manuscript's `o(|R|)` term. -/
theorem p13Node56NetError_div_remainder_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (windowSize remainderSize primitiveSize : Nat)
    (residual : ι → P13Node24RefinementResidual.{u})
    (orderTop : Filter.Tendsto
      (fun i => (residual i).ctx.G.object.input.vertices.card)
      l Filter.atTop)
    (windowFixed : ∀ i,
      (residual i).node21.previous.windowSize = windowSize)
    (remainderFixed : ∀ i,
      (residual i).node21.previous.remainderSize = remainderSize)
    (primitiveFixed : ∀ i,
      (residual i).node21.previous.primitiveSize = primitiveSize) :
    Filter.Tendsto
      (fun i => p13Node56NetError (residual i) /
        ((p13RemainderVertices (residual i).ctx).card : ℝ))
      l (nhds 0) := by
  refine squeeze_zero'
    (g := fun i => p13Node48RankError (residual i) /
      ((p13RemainderVertices (residual i).ctx).card : ℝ)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun i =>
      div_nonneg (p13Node56NetError_nonnegative (residual i)) (by positivity)
  · exact Filter.Eventually.of_forall fun i =>
      div_le_div_of_nonneg_right
        (p13Node56NetError_le_node48RankError (residual i)) (by positivity)
  · exact p13Node48RankError_div_remainder_tendsto_zero
      windowSize remainderSize primitiveSize residual orderTop
      windowFixed remainderFixed primitiveFixed

/-- The complete asymptotic strict-quarter conclusion printed at node `[56]`.
It consumes a family of node-[56] outputs; it does not reconstruct them. -/
theorem p13Node56_strictQuarter_eventually
    {ι : Type*} {l : Filter ι}
    (windowSize remainderSize primitiveSize : Nat)
    (residual : ι → P13Node24RefinementResidual.{u})
    (node56 : ∀ i, P13Node56Output (residual i))
    (orderTop : Filter.Tendsto
      (fun i => (residual i).ctx.G.object.input.vertices.card)
      l Filter.atTop)
    (windowFixed : ∀ i,
      (residual i).node21.previous.windowSize = windowSize)
    (remainderFixed : ∀ i,
      (residual i).node21.previous.remainderSize = remainderSize)
    (primitiveFixed : ∀ i,
      (residual i).node21.previous.primitiveSize = primitiveSize) :
    ∀ᶠ i in l,
      (p13NetDeficiencyNumerator (residual i).ctx : ℝ) /
          (p13RemainderVertices (residual i).ctx).card < 1 / 4 := by
  have errorZero := p13Node56NetError_div_remainder_tendsto_zero
    windowSize remainderSize primitiveSize residual orderTop
    windowFixed remainderFixed primitiveFixed
  have gapPositive : 0 < (1 / 4 : ℝ) - p13Node24TauWindow := by
    norm_num [p13Node24TauWindow, p13Node24ThetaWindow,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have errorSmall : ∀ᶠ i in l,
      p13Node56NetError (residual i) /
          ((p13RemainderVertices (residual i).ctx).card : ℝ) <
        (1 / 4 : ℝ) - p13Node24TauWindow :=
    errorZero.eventually (Iio_mem_nhds gapPositive)
  have remainderLarge :=
    p13Node48_remainder_quarter_density_eventually residual orderTop
  filter_upwards [errorSmall, remainderLarge] with i errorSmallI remainderLargeI
  have orderPositive :
      (0 : ℝ) < (residual i).ctx.G.object.input.vertices.card := by
    exact_mod_cast (show 0 < (residual i).ctx.G.object.input.vertices.card by
      have := (residual i).node25.thirteen_le_order
      omega)
  have remainderPositive :
      (0 : ℝ) < (p13RemainderVertices (residual i).ctx).card := by
    nlinarith
  have normalizedCap :
      (p13NetDeficiencyNumerator (residual i).ctx : ℝ) /
          (p13RemainderVertices (residual i).ctx).card ≤
        p13Node24TauWindow +
          p13Node56NetError (residual i) /
            (p13RemainderVertices (residual i).ctx).card := by
    rw [div_le_iff₀ remainderPositive]
    calc
      (p13NetDeficiencyNumerator (residual i).ctx : ℝ) ≤
          p13Node24TauWindow *
              (p13RemainderVertices (residual i).ctx).card +
            p13Node56NetError (residual i) := (node56 i).netCap
      _ = (p13Node24TauWindow +
            p13Node56NetError (residual i) /
              (p13RemainderVertices (residual i).ctx).card) *
            (p13RemainderVertices (residual i).ctx).card := by
        field_simp [ne_of_gt remainderPositive]
  linarith

end Erdos64EG.Internal
