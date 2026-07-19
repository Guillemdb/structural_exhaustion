import Erdos64EG.P13PartIWindowDensityTriage
import Erdos64EG.CT15BaselineSpineDemand
import Erdos64EG.P13Nodes35To47Refinement
import Erdos64EG.P13Node24DensityArithmetic
import Erdos64EG.P13Node24AsymptoticTransport
import Mathlib.Data.Set.PowersetCard
import StructuralExhaustion.Core.DensityAsymptoticTransport
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Graph.ConditionalFibreProductCost

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [48]: exact finite forced-curvature accounting

The manuscript writes the wedge floor and its curvature cost with an
`o(|R|)` error.  On the actual bounded-surplus branch the corresponding
finite statement has the total degree surplus as its explicit error term.
This file proves that statement from the same node-[24] coverage residual and
node-[47] rank prefix.  It scans no new universe.

The numerical inequality below is deliberately kept separate from the claim
that rank independence realizes a simultaneous product of curvature states.
The latter is a stronger semantic requirement.  This file retains its exact
payload and consequences only as conditional support; it exposes no absence
outcome because the original diagram has only `[47] -> [48] -> [49]`.
-/

/-- Common denominator after eliminating the thirteen vertices occupied by
each selected `P₁₃` window from the exact density cap. -/
def p13WindowRemainderRateDenominator : Nat :=
  p13WindowDensityRateNumerator -
    13 * p13WindowDensitySkeletonNumerator

/-- Exact scaled window-only wedge-rate numerator. -/
def p13WindowWedgeRateNumerator : Nat :=
  3 * p13WindowRemainderRateDenominator -
    30 * p13WindowDensitySkeletonNumerator

/-- The manuscript's exact flatness entropy cost per independent curvature
coordinate.  The finite counts are certified at node `[21]`; node `[48]`
only converts their ratio into budget units. -/
noncomputable def p13CurvatureEntropyCost : ℝ :=
  Real.logb 2 ((543958 : ℝ) / 111286)

/-- Exact window-only curvature density used in the node-[48] cost. -/
noncomputable def p13WindowCurvatureDensity : ℝ :=
  (p13WindowWedgeRateNumerator : ℝ) /
    p13WindowRemainderRateDenominator

/-- Exact version of the printed window-only node-[48] constant. -/
noncomputable def p13WindowForcedCurvatureCost : ℝ :=
  p13CurvatureEntropyCost * p13WindowCurvatureDensity

theorem p13CurvatureEntropyCost_nonneg :
    0 ≤ p13CurvatureEntropyCost := by
  apply Real.logb_nonneg (by norm_num)
  norm_num [p13CurvatureEntropyCost]

/-- The constants are positive and have the literal values used by the
finite arithmetic proof. -/
theorem p13Window_forcedCost_constants :
    p13WindowRemainderRateDenominator = 98608581006 ∧
      p13WindowWedgeRateNumerator = 250825743018 := by
  norm_num [p13WindowRemainderRateDenominator,
    p13WindowWedgeRateNumerator, p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator]

/-- Eliminate the occupied window vertices from node `[24]`'s exact density
cap. -/
theorem p13Window_densityCap_remainderForm
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    p13WindowRemainderRateDenominator * p13 ctx ≤
      p13WindowDensitySkeletonNumerator *
        (p13RemainderVertices ctx).card := by
  have partition := (node24.globalRankPrefix).remainder.exactPartition
  have density := node24.packingDensityCap
  norm_num [p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator] at density ⊢
  nlinarith

/-- Exact node-[30] wedge floor after the node-[24] packing cap is substituted.
The only error is twice the total surplus, in the same scaled integer units.
-/
theorem p13Window_scaledWedgeCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    p13WindowWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  let profile := p13RemainderCurvatureProfile ctx
  have density := p13Window_densityCap_remainderForm node24
  have deficiency :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  have wedge := profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  have surplusPartition :=
    Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus ctx.G.object
  dsimp [profile] at wedge
  change 3 * (p13RemainderVertices ctx).card ≤
    (p13RemainderCurvatureProfile ctx).wedgeCount +
      2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency at wedge
  norm_num [p13WindowWedgeRateNumerator,
    p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator] at density ⊢
  have surplusLe :
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    omega
  have errorCover :
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        2 * 98608581006 *
          (15 * p13 ctx +
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object) :=
        Nat.mul_le_mul_left _ deficiency
      _ = 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by ring
      _ ≤ 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ surplusLe) _
  have wedgeWithBudget :
      3 * 98608581006 * (p13RemainderVertices ctx).card ≤
        98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      3 * 98608581006 * (p13RemainderVertices ctx).card =
          98608581006 * (3 * (p13RemainderVertices ctx).card) := by ring
      _ ≤ 98608581006 *
          ((p13RemainderCurvatureProfile ctx).wedgeCount +
            2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency) :=
        Nat.mul_le_mul_left _ wedge
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          2 * 98608581006 *
            (p13RemainderCurvatureProfile ctx).positiveDeficiency := by ring
      _ ≤ 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          (30 * 98608581006 * p13 ctx +
            2 * 98608581006 *
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) :=
        Nat.add_le_add_left errorCover _
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by ring
  have densityScaled :
      30 * 98608581006 * p13 ctx ≤
        30 * 1500000000 * (p13RemainderVertices ctx).card := by
    calc
      30 * 98608581006 * p13 ctx =
          30 * (98608581006 * p13 ctx) := by ring
      _ ≤ 30 * (1500000000 * (p13RemainderVertices ctx).card) :=
        Nat.mul_le_mul_left 30 density
      _ = 30 * 1500000000 * (p13RemainderVertices ctx).card := by ring
  apply (Nat.add_le_add_iff_right).mp
  calc
    250825743018 * (p13RemainderVertices ctx).card +
        30 * 1500000000 * (p13RemainderVertices ctx).card =
      3 * 98608581006 * (p13RemainderVertices ctx).card := by ring
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 98608581006 * p13 ctx +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
      wedgeWithBudget
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 1500000000 * (p13RemainderVertices ctx).card +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left densityScaled _) _
    _ = (98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        197217162012 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
        30 * 1500000000 * (p13RemainderVertices ctx).card := by ring

/-- Exact sharper numerator on the separately proved high-entropy density
branch. -/
def p13HighEntropyWedgeRateNumerator : Nat := 253825743018

/-- Exact high-entropy curvature density and cost used in the sharper
node-[48] constructor. -/
noncomputable def p13HighEntropyCurvatureDensity : ℝ :=
  (p13HighEntropyWedgeRateNumerator : ℝ) /
    p13WindowRemainderRateDenominator

noncomputable def p13HighEntropyForcedCurvatureCost : ℝ :=
  p13CurvatureEntropyCost * p13HighEntropyCurvatureDensity

/-- The high-entropy cap has the same remainder denominator and a smaller
right-hand rate. -/
theorem p13HighEntropy_densityCap_remainderForm
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (high : node24.highEntropy.conclusion) :
    98608581006 * p13 ctx ≤
      1400000000 * (p13RemainderVertices ctx).card := by
  have partition := node24.globalRankPrefix.remainder.exactPartition
  have highCap : P13HighEntropyFiniteCap ctx node24.coverage.windowCeiling := by
    rwa [node24.highEntropy.conclusionExact] at high
  have density : p13HighEntropyRateNumerator * p13 ctx ≤
      p13HighEntropySkeletonNumerator * ctx.G.object.input.vertices.card :=
    (Nat.mul_le_mul_left p13HighEntropyRateNumerator
      node24.coverage.packing_le).trans highCap
  norm_num [p13HighEntropyRateNumerator,
    p13HighEntropySkeletonNumerator] at density ⊢
  nlinarith

/-- Sharper node-[48] finite magnitude, conditional only on the actual
high-entropy cap and using the same local wedge ledger. -/
theorem p13HighEntropy_scaledWedgeCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (high : node24.highEntropy.conclusion) :
    p13HighEntropyWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  let profile := p13RemainderCurvatureProfile ctx
  have density := p13HighEntropy_densityCap_remainderForm node24 high
  have deficiency :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  have wedge := profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  have surplusPartition :=
    Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus ctx.G.object
  dsimp [profile] at wedge
  change 3 * (p13RemainderVertices ctx).card ≤
    (p13RemainderCurvatureProfile ctx).wedgeCount +
      2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency at wedge
  norm_num [p13HighEntropyWedgeRateNumerator,
    p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator] at density ⊢
  have surplusLe :
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    omega
  have errorCover :
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        2 * 98608581006 *
          (15 * p13 ctx +
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object) :=
        Nat.mul_le_mul_left _ deficiency
      _ = 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by ring
      _ ≤ 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ surplusLe) _
  have wedgeWithBudget :
      3 * 98608581006 * (p13RemainderVertices ctx).card ≤
        98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      3 * 98608581006 * (p13RemainderVertices ctx).card =
          98608581006 * (3 * (p13RemainderVertices ctx).card) := by ring
      _ ≤ 98608581006 *
          ((p13RemainderCurvatureProfile ctx).wedgeCount +
            2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency) :=
        Nat.mul_le_mul_left _ wedge
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          2 * 98608581006 *
            (p13RemainderCurvatureProfile ctx).positiveDeficiency := by ring
      _ ≤ 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          (30 * 98608581006 * p13 ctx +
            2 * 98608581006 *
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) :=
        Nat.add_le_add_left errorCover _
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by ring
  have densityScaled :
      30 * 98608581006 * p13 ctx ≤
        30 * 1400000000 * (p13RemainderVertices ctx).card := by
    calc
      30 * 98608581006 * p13 ctx =
          30 * (98608581006 * p13 ctx) := by ring
      _ ≤ 30 * (1400000000 * (p13RemainderVertices ctx).card) :=
        Nat.mul_le_mul_left 30 density
      _ = 30 * 1400000000 * (p13RemainderVertices ctx).card := by ring
  apply (Nat.add_le_add_iff_right).mp
  calc
    253825743018 * (p13RemainderVertices ctx).card +
        30 * 1400000000 * (p13RemainderVertices ctx).card =
      3 * 98608581006 * (p13RemainderVertices ctx).card := by ring
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 98608581006 * p13 ctx +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
      wedgeWithBudget
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 1400000000 * (p13RemainderVertices ctx).card +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left densityScaled _) _
    _ = (98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        197217162012 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
        30 * 1400000000 * (p13RemainderVertices ctx).card := by ring

/-- Node `[48]` output in rank coordinates.  Node `[47]` identifies the
complete CT15 coordinate count with the literal wedge count, so this is a
pure transport of the preceding theorem. -/
structure VerifiedP13Node48FiniteCost
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) : Type (u + 4)
    extends Core.ExactHandoff node24.globalRankPrefix where
  fullRank :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount
  scaledCost :
    p13WindowWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  highEntropyScaledCost : node24.highEntropy.conclusion →
    p13HighEntropyWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object

/-- Construct the exact finite node-[48] arithmetic from its literal green
predecessors. -/
noncomputable def verifiedP13Node48FiniteCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    VerifiedP13Node48FiniteCost ctx node21 node24 where
  previous := node24.globalRankPrefix
  previousExact := rfl
  fullRank := node24.globalRankPrefix_fullRankCount
  scaledCost := by
    rw [node24.globalRankPrefix_fullRankCount]
    exact p13Window_scaledWedgeCost node24
  highEntropyScaledCost := by
    intro high
    rw [node24.globalRankPrefix_fullRankCount]
    exact p13HighEntropy_scaledWedgeCost node24 high

/-! ## Exact current-frontier node-[47] to node-[48] handoff -/

/-- The literal binary-log/fixed-point scale retained by corrected node [24]. -/
noncomputable def p13Node48NormalizationScale
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale

theorem p13Node48NormalizationScale_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node48NormalizationScale ctx =
      Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale := rfl

/-- Framework-owned square-root envelope for the exact bounded-surplus data
inherited by node [48]. -/
noncomputable def p13Node48SurplusEnvelope
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  Core.QuadraticScaleSplit.boundedRealEnvelope
    (surplusScaleCoefficient residual.node21.previous.windowSize
      residual.node21.previous.remainderSize
      residual.node21.previous.primitiveSize)
    residual.ctx.G.object.input.vertices.card

/-- The actual total surplus on the node-[47] residual lies below that exact
square-root envelope. -/
theorem p13Node48_totalSurplus_le_envelope
    (residual : P13Node24RefinementResidual.{u}) :
    (Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object : ℝ) ≤
      p13Node48SurplusEnvelope residual := by
  simpa [p13Node48SurplusEnvelope, surplusScaleInput] using
    Core.QuadraticScaleSplit.load_cast_le_boundedRealEnvelope
      (surplusScaleInput residual.ctx
        residual.node21.previous.windowSize
        residual.node21.previous.remainderSize
        residual.node21.previous.primitiveSize)
      residual.node30.nearCubic.surplus_sq_le

/-- Once the three authored local thresholds are fixed, their near-cubic
surplus envelope is `o(n)`. This is the uniformity required by the paper's
asymptotic notation; varying thresholds require a separate uniform bound. -/
theorem p13Node48SurplusEnvelope_div_order_tendsto_zero
    (windowSize remainderSize primitiveSize : Nat) :
    Filter.Tendsto
      (fun order : Nat =>
        Core.QuadraticScaleSplit.boundedRealEnvelope
            (surplusScaleCoefficient windowSize remainderSize primitiveSize) order /
          (order : ℝ))
      Filter.atTop (nhds 0) :=
  Core.QuadraticScaleSplit.boundedRealEnvelope_div_order_tendsto_zero _

/-- The corrected node-[24] finite cap, rewritten on the exact remainder of
the accumulated node-[47] branch.  The normalization error is retained rather
than discarded. -/
theorem p13Node48_windowDensity_remainderForm
    (residual : P13Node24RefinementResidual.{u}) :
    p13WindowRemainderRateDenominator * p13 residual.ctx *
        p13Node48NormalizationScale residual.ctx ≤
      p13WindowDensitySkeletonNumerator *
          (p13RemainderVertices residual.ctx).card *
          p13Node48NormalizationScale residual.ctx +
        p13SequentialHotNormalizationError residual.ctx residual.node21 := by
  have density := residual.node24.thetaWindowCorrected
  have partition := p13Remainder_partition residual.ctx
  have density' :
      p13WindowDensityRateNumerator * p13 residual.ctx *
          p13Node48NormalizationScale residual.ctx ≤
        p13WindowDensitySkeletonNumerator *
            residual.ctx.G.object.input.vertices.card *
            p13Node48NormalizationScale residual.ctx +
          p13SequentialHotNormalizationError residual.ctx residual.node21 := by
    rw [p13Node48NormalizationScale_eq]
    simpa only [p13SequentialPrintedSkeletonBits, mul_assoc] using density
  exact Core.DensityAsymptoticTransport.nat_partition_density_with_error
    (by norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator])
    partition density'

/-- Exact current node-[48] finite cost from the genuine node-[47] output.
This is the manuscript's window-rate inequality with the node-[24]
normalization correction and total surplus left explicit. -/
theorem p13Node48_scaledCost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch) :
    p13WindowWedgeRateNumerator *
        (p13RemainderVertices residual.ctx).card *
        p13Node48NormalizationScale residual.ctx ≤
      p13WindowRemainderRateDenominator *
          p13CurvatureTargetRank residual.ctx *
          p13Node48NormalizationScale residual.ctx +
        30 * p13SequentialHotNormalizationError
          residual.ctx residual.node21 +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object *
          p13Node48NormalizationScale residual.ctx := by
  have density := p13Node48_windowDensity_remainderForm residual
  rw [p13,
    ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
    at density
  have wedge := residual.node30.windowFiniteSupply
  rw [node47.fullRank]
  exact Core.DensityAsymptoticTransport.nat_scaled_wedge_with_error
    (by norm_num [p13WindowWedgeRateNumerator,
      p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator,
      p13WindowDensitySkeletonNumerator]) density wedge

/-- The exact positive divisor supplied by node [25]'s nonempty P13 packing. -/
theorem p13Node48NormalizationScale_pos
    (residual : P13Node24RefinementResidual.{u}) :
    0 < p13Node48NormalizationScale residual.ctx := by
  rw [p13Node48NormalizationScale_eq]
  apply Nat.mul_pos
  · exact Nat.log_pos (by omega) (by
      have := residual.node25.thirteen_le_order
      omega)
  · unfold p13ExactHotCertificateScale
    exact Nat.pow_pos (by omega)

/-- Node `[48]`'s exact additive rank error after division by its positive
binary-log certificate scale. -/
noncomputable def p13Node48RankError
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  30 * (p13SequentialHotNormalizationError
      residual.ctx residual.node21 : ℝ) /
      (p13Node48NormalizationScale residual.ctx : ℝ) +
    2 * p13WindowRemainderRateDenominator *
      (Graph.InducedPathWindowLedger.totalSurplus
        residual.ctx.G.object : ℝ)

/-- Uniform graph-order envelope for the normalization part of node `[48]`'s
rank error. -/
noncomputable def p13Node48NormalizationRankErrorEnvelope (order : Nat) : ℝ :=
  30 * p13SequentialHotNormalizationRealEnvelope order /
    ((Nat.log 2 order : ℝ) * (p13ExactHotCertificateScale : ℝ))

theorem p13Node48NormalizationRankErrorEnvelope_div_order_tendsto_zero :
    Filter.Tendsto
      (fun order : Nat =>
        p13Node48NormalizationRankErrorEnvelope order / (order : ℝ))
      Filter.atTop (nhds 0) := by
  have normalized :=
    Core.BinaryLogNormalization.tendsto_div_natCast_mul_natLog_two_nhds_zero
      p13SequentialHotNormalizationRealEnvelope
      p13SequentialHotNormalizationRealEnvelope_isLittleO
  have scaled :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => 30 / (p13ExactHotCertificateScale : ℝ))
      Filter.atTop (nhds (30 / (p13ExactHotCertificateScale : ℝ)))).mul
      normalized
  simpa [p13Node48NormalizationRankErrorEnvelope, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using scaled

theorem p13Node48NormalizationRankError_le_envelope
    (residual : P13Node24RefinementResidual.{u}) :
    30 * (p13SequentialHotNormalizationError
        residual.ctx residual.node21 : ℝ) /
        (p13Node48NormalizationScale residual.ctx : ℝ) ≤
      p13Node48NormalizationRankErrorEnvelope
        residual.ctx.G.object.input.vertices.card := by
  have orderLarge := residual.node25.thirteen_le_order
  have errorBound := p13SequentialHotNormalizationError_real_upper
    residual.ctx residual.node21 (by omega)
  have scaledError :
      (30 : ℝ) * (p13SequentialHotNormalizationError
        residual.ctx residual.node21 : ℝ) ≤
      (30 : ℝ) * p13SequentialHotNormalizationRealEnvelope
        residual.ctx.G.object.input.vertices.card :=
    mul_le_mul_of_nonneg_left errorBound (by norm_num)
  rw [p13Node48NormalizationScale_eq]
  unfold p13Node48NormalizationRankErrorEnvelope
  simpa only [Nat.cast_mul] using div_le_div_of_nonneg_right
    (c := (Nat.log 2 residual.ctx.G.object.input.vertices.card : ℝ) *
      (p13ExactHotCertificateScale : ℝ))
    scaledError
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Complete graph-order-only rank-error envelope at fixed authored local
thresholds. -/
noncomputable def p13Node48ErrorEnvelope
    (windowSize remainderSize primitiveSize order : Nat) : ℝ :=
  p13Node48NormalizationRankErrorEnvelope order +
    2 * p13WindowRemainderRateDenominator *
      Core.QuadraticScaleSplit.boundedRealEnvelope
        (surplusScaleCoefficient windowSize remainderSize primitiveSize) order

theorem p13Node48ErrorEnvelope_div_order_tendsto_zero
    (windowSize remainderSize primitiveSize : Nat) :
    Filter.Tendsto
      (fun order : Nat =>
        p13Node48ErrorEnvelope windowSize remainderSize primitiveSize order /
          (order : ℝ))
      Filter.atTop (nhds 0) := by
  have surplusZero := p13Node48SurplusEnvelope_div_order_tendsto_zero
    windowSize remainderSize primitiveSize
  have scaledSurplus :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => (2 * p13WindowRemainderRateDenominator : ℝ))
      Filter.atTop
      (nhds (2 * p13WindowRemainderRateDenominator : ℝ))).mul surplusZero
  have combined :=
    p13Node48NormalizationRankErrorEnvelope_div_order_tendsto_zero.add
      scaledSurplus
  simpa [p13Node48ErrorEnvelope, add_div, mul_div_assoc, mul_assoc] using combined

theorem p13Node48RankError_le_errorEnvelope
    (residual : P13Node24RefinementResidual.{u}) :
    p13Node48RankError residual ≤
      p13Node48ErrorEnvelope
        residual.node21.previous.windowSize
        residual.node21.previous.remainderSize
        residual.node21.previous.primitiveSize
        residual.ctx.G.object.input.vertices.card := by
  have normalization := p13Node48NormalizationRankError_le_envelope residual
  have surplus := p13Node48_totalSurplus_le_envelope residual
  have scaledSurplus :
      (2 * p13WindowRemainderRateDenominator : ℝ) *
          Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object ≤
        (2 * p13WindowRemainderRateDenominator : ℝ) *
          p13Node48SurplusEnvelope residual :=
    mul_le_mul_of_nonneg_left surplus (by positivity)
  exact add_le_add normalization scaledSurplus

/-- Uniform fixed-threshold family form of node `[48]`'s exact additive
error.  The residual family is never enumerated; only its graph order is used. -/
theorem p13Node48RankError_div_order_tendsto_zero
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
      (fun i => p13Node48RankError (residual i) /
        ((residual i).ctx.G.object.input.vertices.card : ℝ))
      l (nhds 0) := by
  have envelopeZero :=
    (p13Node48ErrorEnvelope_div_order_tendsto_zero
      windowSize remainderSize primitiveSize).comp orderTop
  refine squeeze_zero'
    (g := fun i =>
      p13Node48ErrorEnvelope windowSize remainderSize primitiveSize
          (residual i).ctx.G.object.input.vertices.card /
        ((residual i).ctx.G.object.input.vertices.card : ℝ)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun i => by
      exact div_nonneg (by
        unfold p13Node48RankError
        positivity) (Nat.cast_nonneg _)
  · filter_upwards with i
    have bound := p13Node48RankError_le_errorEnvelope (residual i)
    rw [windowFixed i, remainderFixed i, primitiveFixed i] at bound
    exact div_le_div_of_nonneg_right bound (Nat.cast_nonneg _)
  · simpa [Function.comp_def] using envelopeZero

theorem p13Node48_remainder_quarter_density_eventually
    {ι : Type*} {l : Filter ι}
    (residual : ι → P13Node24RefinementResidual.{u})
    (orderTop : Filter.Tendsto
      (fun i => (residual i).ctx.G.object.input.vertices.card)
      l Filter.atTop) :
    ∀ᶠ i in l,
      (1 / 4 : ℝ) * (residual i).ctx.G.object.input.vertices.card ≤
        ((p13RemainderVertices (residual i).ctx).card : ℝ) := by
  have remainderErrorZero :=
    p13Node24RemainderError_tendsto_zero.comp orderTop
  have gapPositive :
      0 < (1 - 13 * p13Node24ThetaWindow) - (1 / 4 : ℝ) := by
    norm_num [p13Node24ThetaWindow, p13WindowDensitySkeletonNumerator,
      p13WindowDensityRateNumerator]
  have errorSmall : ∀ᶠ i in l,
      p13Node24RemainderError
          (residual i).ctx.G.object.input.vertices.card <
        (1 - 13 * p13Node24ThetaWindow) - (1 / 4 : ℝ) :=
    remainderErrorZero.eventually (Iio_mem_nhds gapPositive)
  filter_upwards [errorSmall] with i errorSmallI
  have ratio := (residual i).node25.ratio_ge_main_sub_oOne
  have quarterLeRatio :
      (1 / 4 : ℝ) ≤
        ((p13RemainderVertices (residual i).ctx).card : ℝ) /
          (residual i).ctx.G.object.input.vertices.card := by
    nlinarith
  have orderPositive :
      (0 : ℝ) < (residual i).ctx.G.object.input.vertices.card := by
    exact_mod_cast (show 0 < (residual i).ctx.G.object.input.vertices.card by
      have := (residual i).node25.thirteen_le_order
      omega)
  exact (le_div_iff₀ orderPositive).mp quarterLeRatio

/-- The exact fixed-threshold node-[48] error is `o(|R|)`, matching the
manuscript's denominator rather than merely the ambient graph order. -/
theorem p13Node48RankError_div_remainder_tendsto_zero
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
      (fun i => p13Node48RankError (residual i) /
        ((p13RemainderVertices (residual i).ctx).card : ℝ))
      l (nhds 0) := by
  apply Core.DensityAsymptoticTransport.tendsto_error_div_remainder_of_lower_density
      (fun i => p13Node48RankError (residual i))
      (fun i => ((p13RemainderVertices (residual i).ctx).card : ℝ))
      (fun i => ((residual i).ctx.G.object.input.vertices.card : ℝ))
      (1 / 4) (by norm_num)
  · exact Filter.Eventually.of_forall fun i => by
      unfold p13Node48RankError
      positivity
  · exact Filter.Eventually.of_forall fun i => by
      exact_mod_cast (show 0 < (residual i).ctx.G.object.input.vertices.card by
        have := (residual i).node25.thirteen_le_order
        omega)
  · exact p13Node48_remainder_quarter_density_eventually residual orderTop
  · exact p13Node48RankError_div_order_tendsto_zero
      windowSize remainderSize primitiveSize residual orderTop
      windowFixed remainderFixed primitiveFixed

/-- Unscaled finite node-[48] cost, obtained from the exact node-[47]
predecessor without dropping either normalization or surplus error. -/
theorem p13Node48_cost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch) :
    (p13WindowWedgeRateNumerator : ℝ) *
        (p13RemainderVertices residual.ctx).card ≤
      (p13WindowRemainderRateDenominator : ℝ) *
          p13CurvatureTargetRank residual.ctx +
        p13Node48RankError residual := by
  have scaledNat := p13Node48_scaledCost_from_node47 residual branch node47
  have scaledReal :
      ((p13WindowWedgeRateNumerator : ℝ) *
          (p13RemainderVertices residual.ctx).card) *
          p13Node48NormalizationScale residual.ctx ≤
        ((p13WindowRemainderRateDenominator : ℝ) *
          p13CurvatureTargetRank residual.ctx) *
            p13Node48NormalizationScale residual.ctx +
          (30 * p13SequentialHotNormalizationError
            residual.ctx residual.node21 : Nat) +
          ((2 * p13WindowRemainderRateDenominator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              residual.ctx.G.object) *
                p13Node48NormalizationScale residual.ctx := by
    exact_mod_cast scaledNat
  have normalized :=
    Core.DensityAsymptoticTransport.scaled_le_main_add_error_div
      (show (0 : ℝ) < p13Node48NormalizationScale residual.ctx by
        exact_mod_cast p13Node48NormalizationScale_pos residual)
      scaledReal
  simpa [p13Node48RankError, mul_assoc, add_assoc] using normalized

/-- The sharper high-entropy coefficient is conditional on the exact
downstream requirement emitted by node [24], on the same accumulated
residual. -/
theorem p13Node48_highEntropyScaledCost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (high : P13Node24HighEntropyDownstreamRequirement
      residual.ctx residual.node21) :
    p13HighEntropyWedgeRateNumerator *
        (p13RemainderVertices residual.ctx).card *
        p13Node48NormalizationScale residual.ctx ≤
      p13WindowRemainderRateDenominator *
          p13CurvatureTargetRank residual.ctx *
          p13Node48NormalizationScale residual.ctx +
        30 * p13SequentialHotNormalizationError
          residual.ctx residual.node21 +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object *
          p13Node48NormalizationScale residual.ctx := by
  unfold P13Node24HighEntropyDownstreamRequirement at high
  have partition := p13Remainder_partition residual.ctx
  have density :
      p13WindowRemainderRateDenominator * p13 residual.ctx *
          p13Node48NormalizationScale residual.ctx ≤
        p13HighEntropySkeletonNumerator *
            (p13RemainderVertices residual.ctx).card *
            p13Node48NormalizationScale residual.ctx +
          p13SequentialHotNormalizationError residual.ctx residual.node21 := by
    have high' :
        p13HighEntropyRateNumerator * p13 residual.ctx *
            p13Node48NormalizationScale residual.ctx ≤
          p13HighEntropySkeletonNumerator *
              residual.ctx.G.object.input.vertices.card *
              p13Node48NormalizationScale residual.ctx +
            p13SequentialHotNormalizationError residual.ctx residual.node21 := by
      rw [p13Node48NormalizationScale_eq]
      simpa only [mul_assoc] using high
    exact Core.DensityAsymptoticTransport.nat_partition_density_with_error
      (by norm_num [p13HighEntropyRateNumerator,
        p13HighEntropySkeletonNumerator,
        p13WindowRemainderRateDenominator,
        p13WindowDensityRateNumerator,
        p13WindowDensitySkeletonNumerator]) partition high'
  rw [p13,
    ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
    at density
  have wedge := residual.node30.windowFiniteSupply
  rw [node47.fullRank]
  exact Core.DensityAsymptoticTransport.nat_scaled_wedge_with_error
    (by norm_num [p13HighEntropyWedgeRateNumerator,
      p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator,
      p13WindowDensitySkeletonNumerator,
      p13HighEntropySkeletonNumerator]) density wedge

/-- The high-entropy strengthening has the same exact additive error after
division by the common positive scale. -/
theorem p13Node48_highEntropyCost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (high : P13Node24HighEntropyDownstreamRequirement
      residual.ctx residual.node21) :
    (p13HighEntropyWedgeRateNumerator : ℝ) *
        (p13RemainderVertices residual.ctx).card ≤
      (p13WindowRemainderRateDenominator : ℝ) *
          p13CurvatureTargetRank residual.ctx +
        p13Node48RankError residual := by
  have scaledNat :=
    p13Node48_highEntropyScaledCost_from_node47 residual branch node47 high
  have scaledReal :
      ((p13HighEntropyWedgeRateNumerator : ℝ) *
          (p13RemainderVertices residual.ctx).card) *
          p13Node48NormalizationScale residual.ctx ≤
        ((p13WindowRemainderRateDenominator : ℝ) *
          p13CurvatureTargetRank residual.ctx) *
            p13Node48NormalizationScale residual.ctx +
          (30 * p13SequentialHotNormalizationError
            residual.ctx residual.node21 : Nat) +
          ((2 * p13WindowRemainderRateDenominator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              residual.ctx.G.object) *
                p13Node48NormalizationScale residual.ctx := by
    exact_mod_cast scaledNat
  have normalized :=
    Core.DensityAsymptoticTransport.scaled_le_main_add_error_div
      (show (0 : ℝ) < p13Node48NormalizationScale residual.ctx by
        exact_mod_cast p13Node48NormalizationScale_pos residual)
      scaledReal
  simpa [p13Node48RankError, mul_assoc, add_assoc] using normalized

/-- The exact finite form of the manuscript's window-only forced curvature
cost.  Its additive term is the already-audited node-[48] rank error, merely
converted into the same entropy units. -/
theorem p13Node48_forcedCurvatureCost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch) :
    p13WindowForcedCurvatureCost *
        (p13RemainderVertices residual.ctx).card ≤
      p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
        (p13CurvatureEntropyCost /
          p13WindowRemainderRateDenominator) *
            p13Node48RankError residual := by
  have rankCost := p13Node48_cost_from_node47 residual branch node47
  have denominatorPositive :
      (0 : ℝ) < p13WindowRemainderRateDenominator := by
    norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have normalized :
      p13WindowCurvatureDensity *
          (p13RemainderVertices residual.ctx).card ≤
        p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual /
            p13WindowRemainderRateDenominator := by
    rw [p13WindowCurvatureDensity]
    calc
      (p13WindowWedgeRateNumerator : ℝ) /
            p13WindowRemainderRateDenominator *
          (p13RemainderVertices residual.ctx).card =
        ((p13WindowWedgeRateNumerator : ℝ) *
          (p13RemainderVertices residual.ctx).card) /
            p13WindowRemainderRateDenominator := by ring
      _ ≤ ((p13WindowRemainderRateDenominator : ℝ) *
            p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual) /
            p13WindowRemainderRateDenominator :=
        div_le_div_of_nonneg_right rankCost denominatorPositive.le
      _ = p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual /
            p13WindowRemainderRateDenominator := by
        field_simp
  have scaled := mul_le_mul_of_nonneg_left normalized
    p13CurvatureEntropyCost_nonneg
  simpa [p13WindowForcedCurvatureCost, div_eq_mul_inv,
    mul_add, mul_assoc, mul_left_comm, mul_comm] using scaled

/-- The exact finite high-entropy strengthening on the existing conditional
edge emitted by node `[24]`. -/
theorem p13Node48_highEntropyForcedCurvatureCost_from_node47
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (high : P13Node24HighEntropyDownstreamRequirement
      residual.ctx residual.node21) :
    p13HighEntropyForcedCurvatureCost *
        (p13RemainderVertices residual.ctx).card ≤
      p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
        (p13CurvatureEntropyCost /
          p13WindowRemainderRateDenominator) *
            p13Node48RankError residual := by
  have rankCost :=
    p13Node48_highEntropyCost_from_node47 residual branch node47 high
  have denominatorPositive :
      (0 : ℝ) < p13WindowRemainderRateDenominator := by
    norm_num [p13WindowRemainderRateDenominator,
      p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]
  have normalized :
      p13HighEntropyCurvatureDensity *
          (p13RemainderVertices residual.ctx).card ≤
        p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual /
            p13WindowRemainderRateDenominator := by
    rw [p13HighEntropyCurvatureDensity]
    calc
      (p13HighEntropyWedgeRateNumerator : ℝ) /
            p13WindowRemainderRateDenominator *
          (p13RemainderVertices residual.ctx).card =
        ((p13HighEntropyWedgeRateNumerator : ℝ) *
          (p13RemainderVertices residual.ctx).card) /
            p13WindowRemainderRateDenominator := by ring
      _ ≤ ((p13WindowRemainderRateDenominator : ℝ) *
            p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual) /
            p13WindowRemainderRateDenominator :=
        div_le_div_of_nonneg_right rankCost denominatorPositive.le
      _ = p13CurvatureTargetRank residual.ctx +
          p13Node48RankError residual /
            p13WindowRemainderRateDenominator := by
        field_simp
  have scaled := mul_le_mul_of_nonneg_left normalized
    p13CurvatureEntropyCost_nonneg
  simpa [p13HighEntropyForcedCurvatureCost, div_eq_mul_inv,
    mul_add, mul_assoc, mul_left_comm, mul_comm] using scaled

/-- The exact additive error in the manuscript's entropy-cost units. -/
noncomputable def p13Node48CostError
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  (p13CurvatureEntropyCost / p13WindowRemainderRateDenominator) *
    p13Node48RankError residual

/-- For every fixed authored threshold family, the node-[48] cost error is
`o(|R|)`.  This is a scalar transport of the already proved rank-error
statement and performs no finite-state search. -/
theorem p13Node48CostError_div_remainder_tendsto_zero
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
      (fun i => p13Node48CostError (residual i) /
        ((p13RemainderVertices (residual i).ctx).card : ℝ))
      l (nhds 0) := by
  have rankErrorZero := p13Node48RankError_div_remainder_tendsto_zero
    windowSize remainderSize primitiveSize residual orderTop
      windowFixed remainderFixed primitiveFixed
  have scaled :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ι =>
        p13CurvatureEntropyCost /
          p13WindowRemainderRateDenominator)
      l (nhds (p13CurvatureEntropyCost /
        p13WindowRemainderRateDenominator))).mul rankErrorZero
  simpa [p13Node48CostError, mul_div_assoc] using scaled

/-- Node `[48]`'s complete forced-cost payload indexed by the exact accumulated
node-[47] predecessor.  In accordance with the manuscript, construction and
entropy of the remainder state family begin at node `[49]`; node `[48]` only
converts the inherited full rank and wedge lower bound into cost units. -/
structure VerifiedP13Node48FrontierCost
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch) : Type (u + 4) where
  scaledCost :
    p13WindowWedgeRateNumerator *
        (p13RemainderVertices residual.ctx).card *
        p13Node48NormalizationScale residual.ctx ≤
      p13WindowRemainderRateDenominator *
          p13CurvatureTargetRank residual.ctx *
          p13Node48NormalizationScale residual.ctx +
        30 * p13SequentialHotNormalizationError
          residual.ctx residual.node21 +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object *
          p13Node48NormalizationScale residual.ctx
  highEntropyScaledCost :
    P13Node24HighEntropyDownstreamRequirement residual.ctx residual.node21 →
      p13HighEntropyWedgeRateNumerator *
          (p13RemainderVertices residual.ctx).card *
          p13Node48NormalizationScale residual.ctx ≤
        p13WindowRemainderRateDenominator *
            p13CurvatureTargetRank residual.ctx *
            p13Node48NormalizationScale residual.ctx +
          30 * p13SequentialHotNormalizationError
            residual.ctx residual.node21 +
          2 * p13WindowRemainderRateDenominator *
            Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object *
            p13Node48NormalizationScale residual.ctx
  forcedCost :
    p13WindowForcedCurvatureCost *
        (p13RemainderVertices residual.ctx).card ≤
      p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
        p13Node48CostError residual
  highEntropyForcedCost :
    P13Node24HighEntropyDownstreamRequirement residual.ctx residual.node21 →
      p13HighEntropyForcedCurvatureCost *
          (p13RemainderVertices residual.ctx).card ≤
        p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
          p13Node48CostError residual
  localWork : Nat := 0
  localWorkZero : localWork = 0

noncomputable def P13Node47FullRankResidual.node48
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    (node47 : VerifiedP13Node47FullRankResidual residual branch) :
    VerifiedP13Node48FrontierCost residual branch node47 where
  scaledCost := p13Node48_scaledCost_from_node47 residual branch node47
  highEntropyScaledCost :=
    p13Node48_highEntropyScaledCost_from_node47 residual branch node47
  forcedCost := by
    simpa [p13Node48CostError] using
      p13Node48_forcedCurvatureCost_from_node47 residual branch node47
  highEntropyForcedCost := by
    intro high
    simpa [p13Node48CostError] using
      p13Node48_highEntropyForcedCurvatureCost_from_node47
        residual branch node47 high
  localWork := 0
  localWorkZero := rfl

/-- One literal undirected edge slot on the labelled ambient vertex set. -/
abbrev P13BaselineEdgeSlot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Enumeration.DistinctPair ctx.G.Vertex

/-- The manuscript's actual labelled baseline-skeleton family: a skeleton is
a finite set of distinct undirected edge slots with exactly the authored
baseline edge count. -/
abbrev P13BaselineSkeleton
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Set.powersetCard (P13BaselineEdgeSlot ctx) (baselineSpineEdgeCount ctx)

/-- The literal edge-set skeleton family has exactly the binomial cardinality
used by the manuscript budget. -/
theorem p13BaselineSkeleton_natCard
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat.card (P13BaselineSkeleton ctx) = baselineSpineStateCount ctx := by
  let edgeSlots := Core.Enumeration.distinctPairs ctx.G.object.input.vertices
  rw [Set.powersetCard.card, Core.Enumeration.natCard_eq edgeSlots]
  rw [show edgeSlots.card =
      Nat.choose ctx.G.object.input.vertices.card 2 by
    exact Core.Enumeration.distinctPairs_card ctx.G.object.input.vertices]
  rfl

structure P13CurvatureProductCostRealization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) : Type (u + 4) where
  previous : VerifiedP13Node48FiniteCost ctx node21 node24
  State : Type u
  states : Core.OrderedCollection State
  context : State →
    Graph.PackedBoundariedGluing.Context ctx.G.Vertex
  accepts : P13CurvatureCoordinate ctx → State → Bool
  responseSemantic : ∀ coordinate state,
    accepts coordinate state =
      (p13CurvatureResponseProfile ctx).responseSystem.response
        coordinate (context state)
  contextInjective : Function.Injective context
  contextSkeleton :
    Graph.PackedBoundariedGluing.Context ctx.G.Vertex →
      P13BaselineSkeleton ctx
  contextSkeletonInjectiveOnStates :
    Function.Injective (fun state ↦ contextSkeleton (context state))
  ledger :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := State
      Coordinate := P13CurvatureCoordinate ctx
      states := states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    Graph.ConditionalFibreProductCost.Profile.Ledger profile
      profile.states.values profile.coordinates.values
  finalNonempty :
    0 < ledger.finalStates.length

namespace P13CurvatureProductCostRealization

/-- The supplied state list fits in the exact labelled-skeleton family because
its duplicate-free entries have an injective graph-owned skeleton code. -/
theorem states_length_le_baseline
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    realized.states.values.length ≤ baselineSpineStateCount ctx := by
  have codesNodup :
      (realized.states.values.map
        (fun state ↦ realized.contextSkeleton (realized.context state))).Nodup :=
    realized.states.nodup.map realized.contextSkeletonInjectiveOnStates
  let edgeSlots := Core.Enumeration.distinctPairs
    ctx.G.object.input.vertices
  calc
    realized.states.values.length ≤
        Nat.choose edgeSlots.card (baselineSpineEdgeCount ctx) :=
      by
        simpa using
          Core.Enumeration.powersetCard_list_length_le edgeSlots
            (baselineSpineEdgeCount ctx) _ codesNodup
    _ = baselineSpineStateCount ctx := by
      rw [show edgeSlots.card = baselineSpineEdgeSlots ctx by
        exact Core.Enumeration.distinctPairs_card
          ctx.G.object.input.vertices]
      rfl

/-- Assemble the generic conditional-fibre certificate from the actual local
ledger and the derived labelled-skeleton capacity. -/
noncomputable def certificate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := realized.State
      Coordinate := P13CurvatureCoordinate ctx
      states := realized.states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := realized.accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    Graph.ConditionalFibreProductCost.Profile.Certificate profile := by
  dsimp
  exact {
    ledger := realized.ledger
    startCapacity := realized.states_length_le_baseline
    finalNonempty := realized.finalNonempty
  }

/-- The graph-owned local conditional-fibre ledger, rather than CT15
nonidentification alone, is what yields the exact multiplicative cost. -/
theorem safeFlatProductBound
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    543958 ^ (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card ≤
      111286 ^ (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card *
        baselineSpineStateCount ctx := by
  let profile : Graph.ConditionalFibreProductCost.Profile := {
    State := realized.State
    Coordinate := P13CurvatureCoordinate ctx
    states := realized.states
    coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
    accepts := realized.accepts
    safe := 543958
    flat := 111286
    skeletonCount := baselineSpineStateCount ctx
  }
  have product :=
    Graph.ConditionalFibreProductCost.Profile.Certificate.power_le_flat_mul_skeleton
      profile realized.certificate
  change 543958 ^ (p13CurvatureCoordinates ctx).card ≤
    111286 ^ (p13CurvatureCoordinates ctx).card *
      baselineSpineStateCount ctx
  simpa [profile, FinEnum.toOrderedCollection_length] using product

/-- The realized product ledger checks only its supplied local state list
against its supplied curvature-coordinate schedule. -/
theorem localChecks_le_state_mul_coordinate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := realized.State
      Coordinate := P13CurvatureCoordinate ctx
      states := realized.states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := realized.accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    profile.checks ≤
      profile.states.values.length * profile.coordinates.values.length := by
  dsimp
  exact Core.ConditionalFibreProductCost.Profile.checks_le_state_mul_coordinate _

end P13CurvatureProductCostRealization

end Erdos64EG.Internal
