import Erdos64EG.P13SequentialWeightedHotColdLedger
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.BinaryLogNormalization
import StructuralExhaustion.Core.DiscreteLinearLittleO
import StructuralExhaustion.Core.NearCubicSkeletonAsymptotics

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact finite normalization of the sequential hot payment

The manuscript's density coefficient is asymptotic.  This file keeps its two
finite corrections explicit: at most thirty discarded dyadic scales per hot
window, and the difference between the exact labelled-skeleton bit count and
the printed `1.5 n log₂ n` main term.  Dropping either correction would turn
the paper's `o(n)` into a false error-free finite inequality.
-/

noncomputable def p13ExactHotCertificateScale : Nat :=
  2 ^ p13ExactWeightedRateCertificate.steps

noncomputable def p13SequentialHotScaleTotal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  aggregate.capacityProfile.weightSum fun owner =>
    (aggregate.retained.get owner).package.scaleMultiplicity

noncomputable def p13SequentialHotScaleLoss
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  aggregate.capacityProfile.weightSum fun owner =>
    (aggregate.retained.get owner).package.scaleLoss

/-- Exact bit count used by the powered aggregate capacity. -/
noncomputable def p13SequentialPoweredSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  Nat.log 2 ((max 1 (baselineSpineStateCount ctx)) ^
    (1000000000 * p13ExactHotCertificateScale))

/-- Main printed skeleton term, at the same fixed-point and rate denominator. -/
noncomputable def p13SequentialPrintedSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card *
    Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale

/-- Exact finite correction to the printed normalized hot budget. -/
noncomputable def p13SequentialHotNormalizationError
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  (p13SequentialPoweredSkeletonBits ctx - p13SequentialPrintedSkeletonBits ctx) +
    p13WindowDensityRateNumerator * p13SequentialHotScaleLoss ctx node21 *
      p13ExactHotCertificateScale

/-- The retained multiplicities and their explicit losses partition all
available dyadic scales owner by owner. -/
theorem p13SequentialHotScaleTotal_add_loss
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13SequentialHotScaleTotal ctx node21 +
        p13SequentialHotScaleLoss ctx node21 =
      (p13SequentialWeightedHotWindows ctx node21).length *
        Nat.log 2 ctx.G.object.input.vertices.card := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  rw [← p13SequentialFinal_retainedCount ctx node21]
  change aggregate.capacityProfile.weightSum (fun owner =>
      (aggregate.retained.get owner).package.scaleMultiplicity) +
      aggregate.capacityProfile.weightSum (fun owner =>
        (aggregate.retained.get owner).package.scaleLoss) = _
  rw [← aggregate.capacityProfile.weightSum_add]
  calc
    aggregate.capacityProfile.weightSum (fun owner =>
        (aggregate.retained.get owner).package.scaleMultiplicity +
          (aggregate.retained.get owner).package.scaleLoss) =
        aggregate.capacityProfile.weightSum (fun _ =>
          Nat.log 2 ctx.G.object.input.vertices.card) := by
      apply congrArg
      funext owner
      exact (aggregate.retained.get owner).package.scaleCountExact
    _ = aggregate.capacityProfile.owners.card *
        Nat.log 2 ctx.G.object.input.vertices.card :=
      aggregate.capacityProfile.weightSum_const _
    _ = aggregate.retained.length *
        Nat.log 2 ctx.G.object.input.vertices.card := by
      simp [P13SequentialHotAggregate.capacityProfile]

/-- The total discarded-scale correction is at most thirty per retained hot
window. -/
theorem p13SequentialHotScaleLoss_le
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13SequentialHotScaleLoss ctx node21 ≤
      30 * (p13SequentialWeightedHotWindows ctx node21).length := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  rw [← p13SequentialFinal_retainedCount ctx node21]
  calc
    aggregate.capacityProfile.weightSum (fun owner =>
        (aggregate.retained.get owner).package.scaleLoss) ≤
        aggregate.capacityProfile.weightSum (fun _ => 30) :=
      aggregate.capacityProfile.weightSum_mono fun owner =>
        (aggregate.retained.get owner).package.scaleLossBound
    _ = aggregate.capacityProfile.owners.card * 30 :=
      aggregate.capacityProfile.weightSum_const 30
    _ = 30 * aggregate.retained.length := by
      simp [P13SequentialHotAggregate.capacityProfile, Nat.mul_comm]

/-- Explicit linear upper bound for the discarded-scale summand. -/
theorem p13SequentialScaleLossBits_le
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13WindowDensityRateNumerator * p13SequentialHotScaleLoss ctx node21 *
        p13ExactHotCertificateScale ≤
      p13WindowDensityRateNumerator * 30 *
        ctx.G.object.input.vertices.card * p13ExactHotCertificateScale := by
  have loss := p13SequentialHotScaleLoss_le ctx node21
  have hot_le_packing :
      (p13SequentialWeightedHotWindows ctx node21).length ≤ p13 ctx := by
    have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
    omega
  have packing_le_vertices : p13 ctx ≤ ctx.G.object.input.vertices.card := by
    have packed := thirteen_mul_p13_le_vertexCount ctx
    omega
  have core : p13SequentialHotScaleLoss ctx node21 ≤
      30 * ctx.G.object.input.vertices.card :=
    loss.trans ((Nat.mul_le_mul_left 30
      (hot_le_packing.trans packing_le_vertices)))
  have scaled := Nat.mul_le_mul_left p13WindowDensityRateNumerator core
  have powered := Nat.mul_le_mul_right p13ExactHotCertificateScale scaled
  simpa [Nat.mul_assoc] using powered

noncomputable def p13SequentialScaleLossLinearCoefficient : Nat :=
  p13WindowDensityRateNumerator * 30 * p13ExactHotCertificateScale

/-- The explicit linear envelope for the scale-loss correction vanishes after
normalization by `n log n`. -/
theorem p13SequentialScaleLossEnvelope_isLittleO :
    (fun n : Nat => (p13SequentialScaleLossLinearCoefficient : ℝ) * n) =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) :=
  Core.DiscreteLinearLittleO.const_mul_natCast_isLittleO_natCast_mul_log _

noncomputable def p13SequentialSkeletonRealErrorEnvelope (n : Nat) : ℝ :=
  (1000000000 * p13ExactHotCertificateScale : Nat) *
    ((3 : ℝ) * n + Real.log (n : ℝ) + 1)

/-- Explicit real-log upper bound for the exact powered skeleton bit count.
The leading term is precisely the manuscript's `3/2 n log n`; all remaining
terms are in `p13SequentialSkeletonRealErrorEnvelope`. -/
theorem p13SequentialPoweredSkeletonBits_real_upper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13SequentialPoweredSkeletonBits ctx : ℝ) * Real.log 2 ≤
      (1000000000 * p13ExactHotCertificateScale : Nat) *
          ((3 / 2 : ℝ) * ctx.G.object.input.vertices.card *
            Real.log ctx.G.object.input.vertices.card) +
        p13SequentialSkeletonRealErrorEnvelope
          ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  let slots := Nat.choose n 2
  let edges := (3 * n + 1) / 2
  let skeletons := Nat.choose slots edges
  let exponent := 1000000000 * p13ExactHotCertificateScale
  have edgesPos : 0 < edges := by dsimp [edges]; omega
  have edgesLeSlots : edges ≤ slots := by
    dsimp [edges, slots]
    rw [Nat.choose_two_right]
    apply Nat.div_le_div_right
    calc
      3 * n + 1 ≤ 4 * n := by omega
      _ ≤ n * (n - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (show 4 ≤ n - 1 by omega)
  have skeletonsPos : 0 < skeletons := Nat.choose_pos edgesLeSlots
  have exponentPos : 0 < exponent := by
    dsimp [exponent, p13ExactHotCertificateScale]
    positivity
  have maxExact : max 1 (baselineSpineStateCount ctx) = skeletons := by
    apply max_eq_right
    exact skeletonsPos
  have poweredNonzero : skeletons ^ exponent ≠ 0 := pow_ne_zero _ skeletonsPos.ne'
  have powLog := Nat.pow_log_le_self 2 poweredNonzero
  have powLogReal :
      ((2 ^ Nat.log 2 (skeletons ^ exponent) : Nat) : ℝ) ≤
        ((skeletons ^ exponent : Nat) : ℝ) := by
    exact_mod_cast powLog
  have logged := Real.log_le_log (by positivity : (0 : ℝ) <
      (2 : ℝ) ^ Nat.log 2 (skeletons ^ exponent)) (by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using powLogReal)
  rw [Real.log_pow, Real.log_pow] at logged
  have chooseLog :=
    Core.NearCubicSkeletonAsymptotics.log_choose_edgeSlots_edgeCount_le n hn
  have multiplied := mul_le_mul_of_nonneg_left chooseLog
    (show (0 : ℝ) ≤ exponent by positivity)
  unfold p13SequentialPoweredSkeletonBits
  rw [maxExact]
  change (Nat.log 2 (skeletons ^ exponent) : ℝ) * Real.log 2 ≤ _
  dsimp [p13SequentialSkeletonRealErrorEnvelope]
  nlinarith

/-- The skeleton correction envelope is little-o of `n log n`. -/
theorem p13SequentialSkeletonRealErrorEnvelope_isLittleO :
    p13SequentialSkeletonRealErrorEnvelope =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  unfold p13SequentialSkeletonRealErrorEnvelope
  exact Core.NearCubicSkeletonAsymptotics.skeletonErrorEnvelope_isLittleO.const_mul_left _

/-- The exact leading coefficient after the fixed-point certificate scale is
restored.  It is the manuscript's `3/2` skeleton coefficient. -/
noncomputable def p13SequentialSkeletonRoundingLeadingCoefficient : ℝ :=
  (3 / 2 : ℝ) *
    (1000000000 * p13ExactHotCertificateScale : Nat)

/-- A graph-order-only envelope for both finite corrections in the exact hot
normalization: binary-log rounding of the powered skeleton count and the
discarded-scale loss. -/
noncomputable def p13SequentialHotNormalizationRealEnvelope (n : Nat) : ℝ :=
  p13SequentialSkeletonRealErrorEnvelope n / Real.log 2 +
    p13SequentialSkeletonRoundingLeadingCoefficient * n +
      (p13SequentialScaleLossLinearCoefficient : ℝ) * n

/-- The actual `Nat.sub` normalization error is uniformly bounded by the
graph-order-only real envelope.  In particular this proof does not assume
that the powered skeleton count dominates the printed main term. -/
theorem p13SequentialHotNormalizationError_real_upper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13SequentialHotNormalizationError ctx node21 : ℝ) ≤
      p13SequentialHotNormalizationRealEnvelope
        ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  have nNonzero : n ≠ 0 := by omega
  have poweredUpper := p13SequentialPoweredSkeletonBits_real_upper ctx hn
  have poweredUpper' :
      (p13SequentialPoweredSkeletonBits ctx : ℝ) * Real.log 2 ≤
        p13SequentialSkeletonRoundingLeadingCoefficient * (n : ℝ) *
            Real.log n + p13SequentialSkeletonRealErrorEnvelope n := by
    simpa [n, p13SequentialSkeletonRoundingLeadingCoefficient,
      mul_assoc, mul_comm, mul_left_comm] using poweredUpper
  have printedExact :
      (p13SequentialPrintedSkeletonBits ctx : ℝ) * Real.log 2 =
        p13SequentialSkeletonRoundingLeadingCoefficient * (n : ℝ) *
          ((Nat.log 2 n : ℝ) * Real.log 2) := by
    simp only [p13SequentialPrintedSkeletonBits, n, Nat.cast_mul]
    norm_num [p13WindowDensitySkeletonNumerator,
      p13SequentialSkeletonRoundingLeadingCoefficient]
    ring
  have skeletonErrorNonnegative :
      0 ≤ p13SequentialSkeletonRealErrorEnvelope n := by
    unfold p13SequentialSkeletonRealErrorEnvelope
    have logNonnegative : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    apply mul_nonneg (by positivity)
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have leadingNonnegative :
      0 ≤ p13SequentialSkeletonRoundingLeadingCoefficient := by
    unfold p13SequentialSkeletonRoundingLeadingCoefficient
    positivity
  have skeletonSub :=
    Core.BinaryLogNormalization.natSub_cast_le_roundingEnvelope
      (p13SequentialPoweredSkeletonBits ctx)
      (p13SequentialPrintedSkeletonBits ctx) n
      p13SequentialSkeletonRoundingLeadingCoefficient
      (p13SequentialSkeletonRealErrorEnvelope n) nNonzero
      leadingNonnegative skeletonErrorNonnegative poweredUpper' printedExact
  have scaleLoss := p13SequentialScaleLossBits_le ctx node21
  have scaleLossReal :
      (p13WindowDensityRateNumerator * p13SequentialHotScaleLoss ctx node21 *
          p13ExactHotCertificateScale : Nat) ≤
        p13SequentialScaleLossLinearCoefficient * n := by
    simpa [n, p13SequentialScaleLossLinearCoefficient, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using scaleLoss
  have scaleLossReal' :
      ((p13WindowDensityRateNumerator * p13SequentialHotScaleLoss ctx node21 *
          p13ExactHotCertificateScale : Nat) : ℝ) ≤
        (p13SequentialScaleLossLinearCoefficient : ℝ) * n := by
    exact_mod_cast scaleLossReal
  unfold p13SequentialHotNormalizationError
  rw [Nat.cast_add]
  exact add_le_add skeletonSub scaleLossReal'

/-- The full finite normalization error is `o(n log n)` uniformly in every
graph and every verified node-[21] input of order `n`. -/
theorem p13SequentialHotNormalizationRealEnvelope_isLittleO :
    p13SequentialHotNormalizationRealEnvelope =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have skeletonWithRounding :=
    Core.BinaryLogNormalization.roundingEnvelope_isLittleO
      p13SequentialSkeletonRealErrorEnvelope
      p13SequentialSkeletonRealErrorEnvelope_isLittleO
      p13SequentialSkeletonRoundingLeadingCoefficient
  change (fun n : Nat =>
      p13SequentialSkeletonRealErrorEnvelope n / Real.log 2 +
        p13SequentialSkeletonRoundingLeadingCoefficient * n +
          (p13SequentialScaleLossLinearCoefficient : ℝ) * n) =o[Filter.atTop]
    (fun n : Nat => (n : ℝ) * Real.log (n : ℝ))
  exact skeletonWithRounding.add p13SequentialScaleLossEnvelope_isLittleO

/-- Exact finite, error-bearing hot normalization.  This is the rigorous form
of the paper's window-only `+ o(n)` payment. -/
theorem p13SequentialHot_normalized_with_error
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13WindowDensityRateNumerator *
        (p13SequentialWeightedHotWindows ctx node21).length *
        Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  have powered := aggregate.exactPoweredRate_le_fixedCapacity
  have paid :
      aggregate.capacityProfile.weightSum (fun owner =>
        p13WindowDensityRateNumerator *
          (aggregate.retained.get owner).package.scaleMultiplicity *
            p13ExactHotCertificateScale) ≤
        p13SequentialPoweredSkeletonBits ctx := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two powered
  have rateScale :
      p13WindowDensityRateNumerator * p13SequentialHotScaleTotal ctx node21 *
          p13ExactHotCertificateScale ≤
        p13SequentialPoweredSkeletonBits ctx := by
    simpa [p13SequentialHotScaleTotal, p13ExactHotCertificateScale,
      Core.DependentOwnerGlueCapacity.Profile.weightSum, Finset.mul_sum,
      Finset.sum_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using paid
  have split := p13SequentialHotScaleTotal_add_loss ctx node21
  have expanded :
      p13WindowDensityRateNumerator *
          (p13SequentialWeightedHotWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale =
        p13WindowDensityRateNumerator * p13SequentialHotScaleTotal ctx node21 *
            p13ExactHotCertificateScale +
          p13WindowDensityRateNumerator * p13SequentialHotScaleLoss ctx node21 *
            p13ExactHotCertificateScale := by
    calc
      _ = p13WindowDensityRateNumerator *
          ((p13SequentialWeightedHotWindows ctx node21).length *
            Nat.log 2 ctx.G.object.input.vertices.card) *
          p13ExactHotCertificateScale := by ring
      _ = p13WindowDensityRateNumerator *
          (p13SequentialHotScaleTotal ctx node21 +
            p13SequentialHotScaleLoss ctx node21) *
          p13ExactHotCertificateScale := by rw [split]
      _ = _ := by ring
  rw [expanded]
  unfold p13SequentialHotNormalizationError
  have skeletonRestore :
      p13SequentialPoweredSkeletonBits ctx ≤
        p13SequentialPrintedSkeletonBits ctx +
          (p13SequentialPoweredSkeletonBits ctx -
            p13SequentialPrintedSkeletonBits ctx) := by omega
  omega

/-- Correct finite node-[24] predicate.  Its correction is exactly the
normalization error above; cold-window mass is not hidden in this predicate. -/
def P13WindowDensityFiniteCapWithError
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Prop :=
  p13WindowDensityRateNumerator * p13 ctx *
      Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
    p13SequentialPrintedSkeletonBits ctx +
      p13SequentialHotNormalizationError ctx node21

/-- Before the cold route is discharged, the exact partition gives the
corrected density cap plus the explicit cold payment. -/
theorem p13SequentialTotal_normalized_le_error_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 +
        p13WindowDensityRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale := by
  have hot := p13SequentialHot_normalized_with_error ctx node21
  have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
  calc
    _ = p13WindowDensityRateNumerator *
          (p13SequentialWeightedHotWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale +
        p13WindowDensityRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale := by rw [← partition]; ring
    _ ≤ _ := Nat.add_le_add_right hot _

/-- Corrected node `[23]`: the strict failure of the finite error-bearing
window cap, retaining the exact node-[21] predecessor. -/
structure VerifiedP13Node23FiniteOverflow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    extends Core.ExactHandoff node21 where
  failedCap : ¬P13WindowDensityFiniteCapWithError ctx node21

/-- Node `[23]`'s local density conclusion: the exact node-[22] comparison
selected the strict reverse inequality. -/
theorem VerifiedP13Node23FiniteOverflow.strict
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23FiniteOverflow ctx node21) :
    p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 <
      p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale := by
  exact Nat.lt_of_not_ge node23.failedCap

/-- Corrected node `[24]`: the complementary finite cap with the paper's
`o(n)` correction represented explicitly. -/
structure VerifiedP13Node24FiniteDensityHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    extends Core.ExactHandoff node21 where
  densityCap : P13WindowDensityFiniteCapWithError ctx node21

/-- Corrected node `[22]` is the literal finite comparison, with no Boolean
realization and no ambient enumeration. -/
inductive P13Node22FiniteDensityOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
  | tooLarge (node23 : VerifiedP13Node23FiniteOverflow ctx node21)
  | withinCap (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)

noncomputable def runP13Node22FiniteDensityDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node22FiniteDensityOutcome ctx node21 := by
  by_cases cap : P13WindowDensityFiniteCapWithError ctx node21
  · exact .withinCap ⟨⟨node21, rfl⟩, cap⟩
  · exact .tooLarge ⟨⟨node21, rfl⟩, cap⟩

/-- The corrected overflow branch necessarily contains a sequential cold
window.  This is the exact `[23] → [150]` trigger consumed by the F1--F5
route; no entropy contradiction is assumed. -/
theorem VerifiedP13Node23FiniteOverflow.cold_nonempty
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23FiniteOverflow ctx node21) :
    0 < (p13SequentialWeightedColdWindows ctx node21).length := by
  have total := p13SequentialTotal_normalized_le_error_add_cold ctx node21
  by_contra notPositive
  have coldZero : (p13SequentialWeightedColdWindows ctx node21).length = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  apply node23.failedCap
  unfold P13WindowDensityFiniteCapWithError
  simpa [coldZero] using total

theorem runP13Node22FiniteDensityDecision_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (∃ node23, runP13Node22FiniteDensityDecision ctx node21 = .tooLarge node23) ∨
      (∃ node24, runP13Node22FiniteDensityDecision ctx node21 = .withinCap node24) := by
  cases outcome : runP13Node22FiniteDensityDecision ctx node21 with
  | tooLarge node23 => exact Or.inl ⟨node23, rfl⟩
  | withinCap node24 => exact Or.inr ⟨node24, rfl⟩

namespace VerifiedP13Node24FiniteDensityHandoff

/-- Exact cross-multiplied `theta ≤ theta_win + error` statement.  Division
by `n log₂ n` is deliberately deferred to the asymptotic consumer. -/
theorem thetaWindowWithError
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 :=
  node24.densityCap

/-- Exact large-remainder connector with the normalization error retained.
After division, this is
`|R|/n ≥ 1 - 13 theta_win - o(1)`. -/
theorem remainderWithError
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
        ctx.G.object.input.vertices.card ≤
      p13WindowDensityRateNumerator *
          Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
          (p13RemainderVertices ctx).card +
        13 * (p13SequentialPrintedSkeletonBits ctx +
          p13SequentialHotNormalizationError ctx node21) := by
  have partition := p13Remainder_partition ctx
  have cap := node24.thetaWindowWithError
  let rateScale := p13WindowDensityRateNumerator *
    Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale
  let allowance := p13SequentialPrintedSkeletonBits ctx +
    p13SequentialHotNormalizationError ctx node21
  have cap' : rateScale * p13 ctx ≤ allowance := by
    simpa [rateScale, allowance, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using cap
  calc
    rateScale * ctx.G.object.input.vertices.card =
        rateScale * ((p13RemainderVertices ctx).card + 13 * p13 ctx) := by
      rw [partition]
    _ = rateScale * (p13RemainderVertices ctx).card +
        13 * (rateScale * p13 ctx) := by ring
    _ ≤ rateScale * (p13RemainderVertices ctx).card + 13 * allowance :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 13 cap') _

/-- Exact pre-quarter connector.  The numerical quarter consumer only has to
compare the right side with the retained main-term slack; no error is dropped. -/
theorem seventyThreePackingWithError
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
        (73 * p13 ctx) ≤
      73 * (p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21) := by
  have cap := node24.thetaWindowWithError
  have multiplied := Nat.mul_le_mul_left 73 cap
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using multiplied

end VerifiedP13Node24FiniteDensityHandoff

end Erdos64EG.Internal
