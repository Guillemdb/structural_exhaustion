import Erdos64EG.P13ExactHotNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.FixedPointRepeatedSquareLower

universe u

set_option maxRecDepth 100000

/-! Exact fixed-decimal certificate for the manuscript's longer hot rate. -/

def p13ManuscriptHotRateNumerator : Nat := 11810858100609198
def p13ManuscriptHotRateDenominator : Nat := 10 ^ 14
def p13ManuscriptSkeletonNumerator : Nat := 150000000000000

def p13ExactManuscriptHotRateShifts : List Nat :=
  p13ExactWeightedRateShifts ++ [1, 0, 0, 0, 0, 1, 1, 1]

def p13ExactManuscriptHotRateRun :
    Run p13ExactWeightedRateDenominator p13ExactWeightedRateInitialLower 118 :=
  Run.ofShifts p13ExactWeightedRateDenominator
    p13ExactWeightedRateInitialLower 118 p13ExactManuscriptHotRateShifts

theorem p13ExactManuscriptHotRate_steps :
    p13ExactManuscriptHotRateRun.steps = 42 := by native_decide

theorem p13ExactManuscriptHotRate_finalExponent :
    p13ExactManuscriptHotRateRun.finalExponent = 519447032625287 := by native_decide

theorem p13ExactManuscriptHotRate_finalLower :
    p13ExactWeightedRateDenominator ≤
      p13ExactManuscriptHotRateRun.finalLower := by native_decide

theorem p13ExactManuscriptHotRate_scaledExponent :
    p13ManuscriptHotRateNumerator * 2 ^ p13ExactManuscriptHotRateRun.steps ≤
      p13ManuscriptHotRateDenominator *
        p13ExactManuscriptHotRateRun.finalExponent := by native_decide

private theorem p13ExactManuscriptHotRate_initial_rational :
    (2 : ℚ) ^ 118 * (p13ExactWeightedRateInitialLower : ℚ) /
        p13ExactWeightedRateDenominator ≤
      (p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct := by
  have denominatorPositive : (0 : ℚ) < p13ExactWeightedRateDenominator := by
    norm_num [p13ExactWeightedRateDenominator]
  have flatPositive : (0 : ℚ) < p13BarrierFlatProduct := by
    have : 0 < p13BarrierFlatProduct := by native_decide
    exact_mod_cast this
  apply (div_le_div_iff₀ denominatorPositive flatPositive).2
  exact_mod_cast p13ExactWeightedRate_initial_cross

/-- Exact local certificate for the fixed decimal
`118.10858100609198`. -/
noncomputable def p13ExactManuscriptHotRateCertificate :
    ScaledDyadicRateLower
      ((p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct)
      p13ManuscriptHotRateNumerator p13ManuscriptHotRateDenominator := by
  let ratio : ℚ := (p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct
  have ratioNonnegative : 0 ≤ ratio := by positivity
  have sound := p13ExactManuscriptHotRateRun.sound
    (by norm_num [p13ExactWeightedRateDenominator]) ratio ratioNonnegative
      p13ExactManuscriptHotRate_initial_rational
  have denominatorPositive : (0 : ℚ) < p13ExactWeightedRateDenominator := by
    norm_num [p13ExactWeightedRateDenominator]
  have finalFactor :
      (1 : ℚ) ≤ (p13ExactManuscriptHotRateRun.finalLower : ℚ) /
        p13ExactWeightedRateDenominator := by
    apply (le_div_iff₀ denominatorPositive).2
    exact_mod_cast p13ExactManuscriptHotRate_finalLower
  refine {
    steps := p13ExactManuscriptHotRateRun.steps
    exponent := p13ExactManuscriptHotRateRun.finalExponent
    ratioNonnegative := ratioNonnegative
    powerLower := ?_
    scaledExponent := p13ExactManuscriptHotRate_scaledExponent
  }
  calc
    (2 : ℚ) ^ p13ExactManuscriptHotRateRun.finalExponent =
        (2 : ℚ) ^ p13ExactManuscriptHotRateRun.finalExponent * 1 := by ring
    _ ≤ (2 : ℚ) ^ p13ExactManuscriptHotRateRun.finalExponent *
          ((p13ExactManuscriptHotRateRun.finalLower : ℚ) /
            p13ExactWeightedRateDenominator) :=
      mul_le_mul_of_nonneg_left finalFactor (by positivity)
    _ = (2 : ℚ) ^ p13ExactManuscriptHotRateRun.finalExponent *
          (p13ExactManuscriptHotRateRun.finalLower : ℚ) /
            p13ExactWeightedRateDenominator := by ring
    _ ≤ ratio ^ (2 ^ p13ExactManuscriptHotRateRun.steps) := sound

/-- The unrounded dyadic rate delivered by the same 42-row run.  Keeping this
certificate separate from the fixed decimal records the tiny strict slack
needed by the manuscript's rounded negative-net coefficient. -/
noncomputable def p13ExactManuscriptDyadicRateCertificate :
    ScaledDyadicRateLower
      ((p13BarrierSafeProduct : ℚ) / p13BarrierFlatProduct)
      p13ExactManuscriptHotRateRun.finalExponent
      (2 ^ p13ExactManuscriptHotRateRun.steps) where
  steps := p13ExactManuscriptHotRateRun.steps
  exponent := p13ExactManuscriptHotRateRun.finalExponent
  ratioNonnegative := by positivity
  powerLower := p13ExactManuscriptHotRateCertificate.powerLower
  scaledExponent := le_rfl

theorem P13WeightedLiveWindowPackage.exactManuscriptStatePowerLower
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    2 ^ (p13ManuscriptHotRateNumerator * package.scaleMultiplicity *
        2 ^ p13ExactManuscriptHotRateCertificate.steps) ≤
      package.states.values.length ^
        (p13ManuscriptHotRateDenominator *
          2 ^ p13ExactManuscriptHotRateCertificate.steps) := by
  have powered := p13ExactManuscriptHotRateCertificate.nat_state_power_lower
    (flatPositive := p13Sequential_flatProduct_pos)
    (by simpa [package.safeProductExact, package.flatProductExact] using
      package.product_le)
  rw [package.profileExact] at powered
  exact powered

/-- Package-level powered inequality at the exact, unrounded dyadic rate. -/
theorem P13WeightedLiveWindowPackage.exactManuscriptDyadicStatePowerLower
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    2 ^ (p13ExactManuscriptHotRateRun.finalExponent *
        package.scaleMultiplicity *
        2 ^ p13ExactManuscriptDyadicRateCertificate.steps) ≤
      package.states.values.length ^
        ((2 ^ p13ExactManuscriptHotRateRun.steps) *
          2 ^ p13ExactManuscriptDyadicRateCertificate.steps) := by
  have powered := p13ExactManuscriptDyadicRateCertificate.nat_state_power_lower
    (flatPositive := p13Sequential_flatProduct_pos)
    (by simpa [package.safeProductExact, package.flatProductExact] using
      package.product_le)
  rw [package.profileExact] at powered
  exact powered

noncomputable def p13ExactManuscriptHotCertificateScale : Nat :=
  2 ^ p13ExactManuscriptHotRateCertificate.steps

noncomputable def p13ManuscriptPoweredSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  Nat.log 2 ((max 1 (baselineSpineStateCount ctx)) ^
    (p13ManuscriptHotRateDenominator * p13ExactManuscriptHotCertificateScale))

noncomputable def p13ManuscriptPrintedSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  p13ManuscriptSkeletonNumerator * ctx.G.object.input.vertices.card *
    Nat.log 2 ctx.G.object.input.vertices.card *
      p13ExactManuscriptHotCertificateScale

noncomputable def p13ManuscriptHotNormalizationError
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  (p13ManuscriptPoweredSkeletonBits ctx - p13ManuscriptPrintedSkeletonBits ctx) +
    p13ManuscriptHotRateNumerator * p13SequentialHotScaleLoss ctx node21 *
      p13ExactManuscriptHotCertificateScale

/-- The same recoverable aggregate pays the longer manuscript rate; only the
fixed 42-row rate certificate differs. -/
theorem p13SequentialHot_manuscript_normalized_with_error
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13ManuscriptHotRateNumerator *
        (p13SequentialWeightedHotWindows ctx node21).length *
        Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactManuscriptHotCertificateScale ≤
      p13ManuscriptPrintedSkeletonBits ctx +
        p13ManuscriptHotNormalizationError ctx node21 := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  have codeBound := aggregate.capacityProfile.base_pow_sumWeight_le_codeCard_pow
    2 (p13ManuscriptHotRateDenominator * p13ExactManuscriptHotCertificateScale)
    (fun owner => p13ManuscriptHotRateNumerator *
      (aggregate.retained.get owner).package.scaleMultiplicity *
        p13ExactManuscriptHotCertificateScale) (by
      intro owner
      let package := (aggregate.retained.get owner).package
      have localRate := package.exactManuscriptStatePowerLower
      have localCard : Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
          package.states.values.length := by
        let enumeration := aggregate.localChoices owner
        calc
          Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
              enumeration.card := Core.Enumeration.natCard_eq enumeration
          _ = package.states.values.length := by
            dsimp [enumeration, P13SequentialHotAggregate.localChoices]
            rw [FinEnum.card_ofList]
            · rw [List.dedup_eq_self.mpr package.states.nodup.attach]
              simp
            · intro state
              exact List.mem_attach _ state
      exact localRate.trans_eq (congrArg
        (fun cardinal => cardinal ^
          (p13ManuscriptHotRateDenominator *
            p13ExactManuscriptHotCertificateScale)) localCard.symm))
  have codeCapacityPower := Nat.pow_le_pow_left aggregate.codeCapacity
    (p13ManuscriptHotRateDenominator * p13ExactManuscriptHotCertificateScale)
  have powered := codeBound.trans codeCapacityPower
  have paid :
      aggregate.capacityProfile.weightSum (fun owner =>
        p13ManuscriptHotRateNumerator *
          (aggregate.retained.get owner).package.scaleMultiplicity *
            p13ExactManuscriptHotCertificateScale) ≤
        p13ManuscriptPoweredSkeletonBits ctx := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two powered
  have rateScale :
      p13ManuscriptHotRateNumerator * p13SequentialHotScaleTotal ctx node21 *
          p13ExactManuscriptHotCertificateScale ≤
        p13ManuscriptPoweredSkeletonBits ctx := by
    simpa [p13SequentialHotScaleTotal, p13ExactManuscriptHotCertificateScale,
      Core.DependentOwnerGlueCapacity.Profile.weightSum, Finset.mul_sum,
      Finset.sum_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using paid
  have split := p13SequentialHotScaleTotal_add_loss ctx node21
  have expanded :
      p13ManuscriptHotRateNumerator *
          (p13SequentialWeightedHotWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptHotCertificateScale =
        p13ManuscriptHotRateNumerator * p13SequentialHotScaleTotal ctx node21 *
            p13ExactManuscriptHotCertificateScale +
          p13ManuscriptHotRateNumerator * p13SequentialHotScaleLoss ctx node21 *
            p13ExactManuscriptHotCertificateScale := by
    calc
      _ = p13ManuscriptHotRateNumerator *
          ((p13SequentialWeightedHotWindows ctx node21).length *
            Nat.log 2 ctx.G.object.input.vertices.card) *
          p13ExactManuscriptHotCertificateScale := by ring
      _ = p13ManuscriptHotRateNumerator *
          (p13SequentialHotScaleTotal ctx node21 +
            p13SequentialHotScaleLoss ctx node21) *
          p13ExactManuscriptHotCertificateScale := by rw [split]
      _ = _ := by ring
  rw [expanded]
  unfold p13ManuscriptHotNormalizationError
  have restore : p13ManuscriptPoweredSkeletonBits ctx ≤
      p13ManuscriptPrintedSkeletonBits ctx +
        (p13ManuscriptPoweredSkeletonBits ctx -
          p13ManuscriptPrintedSkeletonBits ctx) := by omega
  omega

/-! ## Exact dyadic accounting for the printed rounded coefficients -/

noncomputable def p13ManuscriptDyadicRateNumerator : Nat :=
  p13ExactManuscriptHotRateRun.finalExponent

noncomputable def p13ManuscriptDyadicRateDenominator : Nat :=
  2 ^ p13ExactManuscriptHotRateRun.steps

noncomputable def p13ManuscriptDyadicSkeletonNumerator : Nat := 3 * 2 ^ 41

@[simp] theorem p13ManuscriptDyadicRateNumerator_exact :
    p13ManuscriptDyadicRateNumerator = 519447032625287 := by
  simp [p13ManuscriptDyadicRateNumerator,
    p13ExactManuscriptHotRate_finalExponent]

@[simp] theorem p13ManuscriptDyadicRateDenominator_exact :
    p13ManuscriptDyadicRateDenominator = 4398046511104 := by
  simp [p13ManuscriptDyadicRateDenominator,
    p13ExactManuscriptHotRate_steps]

@[simp] theorem p13ManuscriptDyadicSkeletonNumerator_exact :
    p13ManuscriptDyadicSkeletonNumerator = 6597069766656 := by
  norm_num [p13ManuscriptDyadicSkeletonNumerator]

noncomputable def p13ExactManuscriptDyadicCertificateScale : Nat :=
  2 ^ p13ExactManuscriptDyadicRateCertificate.steps

noncomputable def p13ManuscriptDyadicPoweredSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  Nat.log 2 ((max 1 (baselineSpineStateCount ctx)) ^
    (p13ManuscriptDyadicRateDenominator *
      p13ExactManuscriptDyadicCertificateScale))

noncomputable def p13ManuscriptDyadicPrintedSkeletonBits
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  p13ManuscriptDyadicSkeletonNumerator * ctx.G.object.input.vertices.card *
    Nat.log 2 ctx.G.object.input.vertices.card *
      p13ExactManuscriptDyadicCertificateScale

noncomputable def p13ManuscriptDyadicHotNormalizationError
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  (p13ManuscriptDyadicPoweredSkeletonBits ctx -
      p13ManuscriptDyadicPrintedSkeletonBits ctx) +
    p13ManuscriptDyadicRateNumerator *
      p13SequentialHotScaleLoss ctx node21 *
        p13ExactManuscriptDyadicCertificateScale

/-- Exact hot payment at the full dyadic exponent of the 42-row certificate.
This is the finite inequality whose two rational specializations round to the
coefficients printed in the manuscript. -/
theorem p13SequentialHot_manuscriptDyadic_normalized_with_error
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13ManuscriptDyadicRateNumerator *
        (p13SequentialWeightedHotWindows ctx node21).length *
        Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactManuscriptDyadicCertificateScale ≤
      p13ManuscriptDyadicPrintedSkeletonBits ctx +
        p13ManuscriptDyadicHotNormalizationError ctx node21 := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  have codeBound := aggregate.capacityProfile.base_pow_sumWeight_le_codeCard_pow
    2 (p13ManuscriptDyadicRateDenominator *
      p13ExactManuscriptDyadicCertificateScale)
    (fun owner => p13ManuscriptDyadicRateNumerator *
      (aggregate.retained.get owner).package.scaleMultiplicity *
        p13ExactManuscriptDyadicCertificateScale) (by
      intro owner
      let package := (aggregate.retained.get owner).package
      have localRate := package.exactManuscriptDyadicStatePowerLower
      have localCard : Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
          package.states.values.length := by
        let enumeration := aggregate.localChoices owner
        calc
          Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
              enumeration.card := Core.Enumeration.natCard_eq enumeration
          _ = package.states.values.length := by
            dsimp [enumeration, P13SequentialHotAggregate.localChoices]
            rw [FinEnum.card_ofList]
            · rw [List.dedup_eq_self.mpr package.states.nodup.attach]
              simp
            · intro state
              exact List.mem_attach _ state
      exact localRate.trans_eq (congrArg
        (fun cardinal => cardinal ^
          (p13ManuscriptDyadicRateDenominator *
            p13ExactManuscriptDyadicCertificateScale)) localCard.symm))
  have codeCapacityPower := Nat.pow_le_pow_left aggregate.codeCapacity
    (p13ManuscriptDyadicRateDenominator *
      p13ExactManuscriptDyadicCertificateScale)
  have powered := codeBound.trans codeCapacityPower
  have paid :
      aggregate.capacityProfile.weightSum (fun owner =>
        p13ManuscriptDyadicRateNumerator *
          (aggregate.retained.get owner).package.scaleMultiplicity *
            p13ExactManuscriptDyadicCertificateScale) ≤
        p13ManuscriptDyadicPoweredSkeletonBits ctx := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two powered
  have rateScale :
      p13ManuscriptDyadicRateNumerator *
          p13SequentialHotScaleTotal ctx node21 *
          p13ExactManuscriptDyadicCertificateScale ≤
        p13ManuscriptDyadicPoweredSkeletonBits ctx := by
    simpa [p13SequentialHotScaleTotal,
      p13ManuscriptDyadicPoweredSkeletonBits,
      Core.DependentOwnerGlueCapacity.Profile.weightSum, Finset.mul_sum,
      Finset.sum_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using paid
  have split := p13SequentialHotScaleTotal_add_loss ctx node21
  have expanded :
      p13ManuscriptDyadicRateNumerator *
          (p13SequentialWeightedHotWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale =
        p13ManuscriptDyadicRateNumerator *
            p13SequentialHotScaleTotal ctx node21 *
            p13ExactManuscriptDyadicCertificateScale +
          p13ManuscriptDyadicRateNumerator *
            p13SequentialHotScaleLoss ctx node21 *
            p13ExactManuscriptDyadicCertificateScale := by
    calc
      _ = p13ManuscriptDyadicRateNumerator *
          ((p13SequentialWeightedHotWindows ctx node21).length *
            Nat.log 2 ctx.G.object.input.vertices.card) *
          p13ExactManuscriptDyadicCertificateScale := by ring
      _ = p13ManuscriptDyadicRateNumerator *
          (p13SequentialHotScaleTotal ctx node21 +
            p13SequentialHotScaleLoss ctx node21) *
          p13ExactManuscriptDyadicCertificateScale := by rw [split]
      _ = _ := by ring
  rw [expanded]
  unfold p13ManuscriptDyadicHotNormalizationError
  have restore : p13ManuscriptDyadicPoweredSkeletonBits ctx ≤
      p13ManuscriptDyadicPrintedSkeletonBits ctx +
        (p13ManuscriptDyadicPoweredSkeletonBits ctx -
          p13ManuscriptDyadicPrintedSkeletonBits ctx) := by omega
  omega

noncomputable def p13ManuscriptDyadicScaleLossLinearCoefficient : Nat :=
  p13ManuscriptDyadicRateNumerator * 30 *
    p13ExactManuscriptDyadicCertificateScale

theorem p13ManuscriptDyadicScaleLossBits_le
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13ManuscriptDyadicRateNumerator *
        p13SequentialHotScaleLoss ctx node21 *
        p13ExactManuscriptDyadicCertificateScale ≤
      p13ManuscriptDyadicScaleLossLinearCoefficient *
        ctx.G.object.input.vertices.card := by
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
    loss.trans (Nat.mul_le_mul_left 30
      (hot_le_packing.trans packing_le_vertices))
  have scaled := Nat.mul_le_mul_left p13ManuscriptDyadicRateNumerator core
  have powered := Nat.mul_le_mul_right
    p13ExactManuscriptDyadicCertificateScale scaled
  simpa [p13ManuscriptDyadicScaleLossLinearCoefficient, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using powered

theorem p13ManuscriptDyadicScaleLossEnvelope_isLittleO :
    (fun n : Nat =>
      (p13ManuscriptDyadicScaleLossLinearCoefficient : ℝ) * n) =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) :=
  Core.DiscreteLinearLittleO.const_mul_natCast_isLittleO_natCast_mul_log _

noncomputable def p13ManuscriptDyadicSkeletonRealErrorEnvelope (n : Nat) : ℝ :=
  (p13ManuscriptDyadicRateDenominator *
      p13ExactManuscriptDyadicCertificateScale : Nat) *
    ((3 : ℝ) * n + Real.log (n : ℝ) + 1)

noncomputable def p13ManuscriptDyadicSkeletonLeadingCoefficient : ℝ :=
  (3 / 2 : ℝ) *
    (p13ManuscriptDyadicRateDenominator *
      p13ExactManuscriptDyadicCertificateScale : Nat)

theorem p13ManuscriptDyadicPoweredSkeletonBits_real_upper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13ManuscriptDyadicPoweredSkeletonBits ctx : ℝ) * Real.log 2 ≤
      p13ManuscriptDyadicSkeletonLeadingCoefficient *
          ctx.G.object.input.vertices.card *
          Real.log ctx.G.object.input.vertices.card +
        p13ManuscriptDyadicSkeletonRealErrorEnvelope
          ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  let slots := Nat.choose n 2
  let edges := (3 * n + 1) / 2
  let skeletons := Nat.choose slots edges
  let exponent := p13ManuscriptDyadicRateDenominator *
    p13ExactManuscriptDyadicCertificateScale
  have edgesPos : 0 < edges := by dsimp [edges]; omega
  have edgesLeSlots : edges ≤ slots := by
    dsimp [edges, slots]
    rw [Nat.choose_two_right]
    apply Nat.div_le_div_right
    calc
      3 * n + 1 ≤ 4 * n := by omega
      _ ≤ n * (n - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left n
          (show 4 ≤ n - 1 by omega)
  have skeletonsPos : 0 < skeletons := Nat.choose_pos edgesLeSlots
  have exponentPos : 0 < exponent := by
    dsimp [exponent, p13ManuscriptDyadicRateDenominator,
      p13ExactManuscriptDyadicCertificateScale]
    positivity
  have maxExact : max 1 (baselineSpineStateCount ctx) = skeletons := by
    apply max_eq_right
    exact skeletonsPos
  have poweredNonzero : skeletons ^ exponent ≠ 0 :=
    pow_ne_zero _ skeletonsPos.ne'
  have powLog := Nat.pow_log_le_self 2 poweredNonzero
  have powLogReal :
      ((2 ^ Nat.log 2 (skeletons ^ exponent) : Nat) : ℝ) ≤
        ((skeletons ^ exponent : Nat) : ℝ) := by exact_mod_cast powLog
  have logged := Real.log_le_log (by positivity : (0 : ℝ) <
      (2 : ℝ) ^ Nat.log 2 (skeletons ^ exponent)) (by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using powLogReal)
  rw [Real.log_pow, Real.log_pow] at logged
  have chooseLog :=
    Core.NearCubicSkeletonAsymptotics.log_choose_edgeSlots_edgeCount_le n hn
  have multiplied := mul_le_mul_of_nonneg_left chooseLog
    (show (0 : ℝ) ≤ exponent by positivity)
  unfold p13ManuscriptDyadicPoweredSkeletonBits
  rw [maxExact]
  change (Nat.log 2 (skeletons ^ exponent) : ℝ) * Real.log 2 ≤ _
  dsimp [p13ManuscriptDyadicSkeletonRealErrorEnvelope,
    p13ManuscriptDyadicSkeletonLeadingCoefficient, exponent]
  nlinarith

theorem p13ManuscriptDyadicSkeletonRealErrorEnvelope_isLittleO :
    p13ManuscriptDyadicSkeletonRealErrorEnvelope =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  unfold p13ManuscriptDyadicSkeletonRealErrorEnvelope
  exact Core.NearCubicSkeletonAsymptotics.skeletonErrorEnvelope_isLittleO.const_mul_left _

noncomputable def p13ManuscriptDyadicHotNormalizationRealEnvelope (n : Nat) : ℝ :=
  p13ManuscriptDyadicSkeletonRealErrorEnvelope n / Real.log 2 +
    p13ManuscriptDyadicSkeletonLeadingCoefficient * n +
      (p13ManuscriptDyadicScaleLossLinearCoefficient : ℝ) * n

theorem p13ManuscriptDyadicHotNormalizationError_real_upper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13ManuscriptDyadicHotNormalizationError ctx node21 : ℝ) ≤
      p13ManuscriptDyadicHotNormalizationRealEnvelope
        ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  have nNonzero : n ≠ 0 := by omega
  have poweredUpper :=
    p13ManuscriptDyadicPoweredSkeletonBits_real_upper ctx hn
  have printedExact :
      (p13ManuscriptDyadicPrintedSkeletonBits ctx : ℝ) * Real.log 2 =
        p13ManuscriptDyadicSkeletonLeadingCoefficient * (n : ℝ) *
          ((Nat.log 2 n : ℝ) * Real.log 2) := by
    simp only [p13ManuscriptDyadicPrintedSkeletonBits, n, Nat.cast_mul]
    norm_num [p13ManuscriptDyadicSkeletonNumerator,
      p13ManuscriptDyadicSkeletonLeadingCoefficient,
      p13ManuscriptDyadicRateDenominator,
      p13ExactManuscriptHotRate_steps]
    ring
  have errorNonnegative :
      0 ≤ p13ManuscriptDyadicSkeletonRealErrorEnvelope n := by
    unfold p13ManuscriptDyadicSkeletonRealErrorEnvelope
    have logNonnegative : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    apply mul_nonneg (by positivity)
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have leadingNonnegative :
      0 ≤ p13ManuscriptDyadicSkeletonLeadingCoefficient := by
    unfold p13ManuscriptDyadicSkeletonLeadingCoefficient
    positivity
  have skeletonSub :=
    Core.BinaryLogNormalization.natSub_cast_le_roundingEnvelope
      (p13ManuscriptDyadicPoweredSkeletonBits ctx)
      (p13ManuscriptDyadicPrintedSkeletonBits ctx) n
      p13ManuscriptDyadicSkeletonLeadingCoefficient
      (p13ManuscriptDyadicSkeletonRealErrorEnvelope n) nNonzero
      leadingNonnegative errorNonnegative poweredUpper printedExact
  have scaleLoss := p13ManuscriptDyadicScaleLossBits_le ctx node21
  have scaleLossReal :
      ((p13ManuscriptDyadicRateNumerator *
          p13SequentialHotScaleLoss ctx node21 *
          p13ExactManuscriptDyadicCertificateScale : Nat) : ℝ) ≤
        (p13ManuscriptDyadicScaleLossLinearCoefficient : ℝ) * n := by
    exact_mod_cast scaleLoss
  unfold p13ManuscriptDyadicHotNormalizationError
  rw [Nat.cast_add]
  exact add_le_add skeletonSub scaleLossReal

theorem p13ManuscriptDyadicHotNormalizationRealEnvelope_isLittleO :
    p13ManuscriptDyadicHotNormalizationRealEnvelope =o[Filter.atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have skeletonWithRounding :=
    Core.BinaryLogNormalization.roundingEnvelope_isLittleO
      p13ManuscriptDyadicSkeletonRealErrorEnvelope
      p13ManuscriptDyadicSkeletonRealErrorEnvelope_isLittleO
      p13ManuscriptDyadicSkeletonLeadingCoefficient
  change (fun n : Nat =>
      p13ManuscriptDyadicSkeletonRealErrorEnvelope n / Real.log 2 +
        p13ManuscriptDyadicSkeletonLeadingCoefficient * n +
          (p13ManuscriptDyadicScaleLossLinearCoefficient : ℝ) * n) =o[Filter.atTop]
    (fun n : Nat => (n : ℝ) * Real.log (n : ℝ))
  exact skeletonWithRounding.add
    p13ManuscriptDyadicScaleLossEnvelope_isLittleO

/-- Shared binary-log normalization turns the `o(n log n)` bit correction
into a zero normalized correction; equivalently, after division by `log n`
it is `o(n)`. -/
theorem p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero :
    Filter.Tendsto
      (fun n : Nat => p13ManuscriptDyadicHotNormalizationRealEnvelope n /
        ((n : ℝ) * (Nat.log 2 n : ℝ)))
      Filter.atTop (nhds 0) :=
  Core.BinaryLogNormalization.tendsto_div_natCast_mul_natLog_two_nhds_zero
    p13ManuscriptDyadicHotNormalizationRealEnvelope
    p13ManuscriptDyadicHotNormalizationRealEnvelope_isLittleO

end Erdos64EG.Internal
