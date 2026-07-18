import Erdos64EG.P13Node24DensityArithmetic
import StructuralExhaustion.Core.DensityAsymptoticTransport

namespace Erdos64EG.Internal

open Filter StructuralExhaustion
open StructuralExhaustion.Core.DensityAsymptoticTransport

universe u

/-!
# Node [24]: asymptotic density transports

This file divides node `[24]`'s exact finite inequality by its positive
binary-log budget.  It proves only the window-density, remainder, and
fractional-linear incidence conclusions.  The manuscript's sharper
high-entropy estimate is not used or asserted here.
-/

/-- The manuscript's window-density main term in the real field. -/
noncomputable def p13Node24ThetaWindow : ℝ :=
  (p13WindowDensitySkeletonNumerator : ℝ) /
    p13WindowDensityRateNumerator

theorem p13Node24ThetaWindow_eq_exact :
    p13Node24ThetaWindow = (p13WindowThetaExact : ℝ) := by
  norm_num [p13Node24ThetaWindow, p13WindowThetaExact,
    p13WindowDensitySkeletonNumerator, p13WindowDensityRateNumerator]

/-- A graph-order-only additive error for the normalized window density. -/
noncomputable def p13Node24ThetaError (n : Nat) : ℝ :=
  (1 / ((p13WindowDensityRateNumerator : ℝ) *
      (p13ExactHotCertificateScale : ℝ))) *
    (p13SequentialHotNormalizationRealEnvelope n /
      ((n : ℝ) * (Nat.log 2 n : ℝ)))

/-- The explicit normalized correction is `o(1)`. -/
theorem p13Node24ThetaError_tendsto_zero :
    Tendsto p13Node24ThetaError atTop (nhds 0) := by
  have normalized :=
    Core.BinaryLogNormalization.tendsto_div_natCast_mul_natLog_two_nhds_zero
      p13SequentialHotNormalizationRealEnvelope
      p13SequentialHotNormalizationRealEnvelope_isLittleO
  unfold p13Node24ThetaError
  simpa using (tendsto_const_nhds.mul normalized)

/-- The unnormalized producer used above is exactly the uniform little-o
envelope established by the finite hot normalization. -/
theorem p13Node24NormalizationEnvelope_isLittleO :
    p13SequentialHotNormalizationRealEnvelope =o[atTop]
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) :=
  p13SequentialHotNormalizationRealEnvelope_isLittleO

/-- The remainder loses thirteen times the normalized packing-density
error, exactly as in the partition `|R| + 13 p₁₃ = n`. -/
noncomputable def p13Node24RemainderError (n : Nat) : ℝ :=
  13 * p13Node24ThetaError n

theorem p13Node24RemainderError_tendsto_zero :
    Tendsto p13Node24RemainderError atTop (nhds 0) := by
  unfold p13Node24RemainderError
  exact remainder_error_tendsto_zero 13 p13Node24ThetaError_tendsto_zero

namespace VerifiedP13Node24FiniteDensityHandoff

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Rigorous normalized form of the paper's
`theta ≤ theta_win + o(1)` conclusion. -/
theorem theta_le_thetaWindow_add_oOne
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13 ctx : ℝ) / ctx.G.object.input.vertices.card ≤
      p13Node24ThetaWindow +
        p13Node24ThetaError ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  let logN := Nat.log 2 n
  have nPositive : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have logNPositiveNat : 0 < logN :=
    Nat.log_pos (show 1 < 2 by omega) (show 2 ≤ n by omega)
  have logNPositive : (0 : ℝ) < logN := by exact_mod_cast logNPositiveNat
  have ratePositive : (0 : ℝ) < p13WindowDensityRateNumerator := by
    norm_num [p13WindowDensityRateNumerator]
  have scalePositive : (0 : ℝ) < p13ExactHotCertificateScale := by
    unfold p13ExactHotCertificateScale
    positivity
  have capNat := node24.thetaWindowCorrected
  have capReal :
      (p13WindowDensityRateNumerator : ℝ) * (p13 ctx : ℝ) * logN *
          p13ExactHotCertificateScale ≤
        (p13SequentialPrintedSkeletonBits ctx : ℝ) +
          (p13SequentialHotNormalizationError ctx node21 : ℝ) := by
    exact_mod_cast capNat
  have errorBound :=
    p13SequentialHotNormalizationError_real_upper ctx node21 hn
  have printedReal :
      (p13SequentialPrintedSkeletonBits ctx : ℝ) =
        (p13WindowDensitySkeletonNumerator : ℝ) * n * logN *
          p13ExactHotCertificateScale := by
    simp [p13SequentialPrintedSkeletonBits, n, logN]
  rw [printedReal] at capReal
  have normalized :=
    Core.BinaryLogNormalization.ratio_le_main_add_normalizedError
      (mass := (p13 ctx : ℝ)) (order := (n : ℝ))
      (rate := (p13WindowDensityRateNumerator : ℝ))
      (main := (p13WindowDensitySkeletonNumerator : ℝ))
      (logScale := (logN : ℝ))
      (certificateScale := (p13ExactHotCertificateScale : ℝ))
      (exactError := (p13SequentialHotNormalizationError ctx node21 : ℝ))
      (envelope := p13SequentialHotNormalizationRealEnvelope n)
      nPositive ratePositive logNPositive scalePositive capReal errorBound
  simpa [p13Node24ThetaWindow, p13Node24ThetaError, n, logN] using normalized

/-- The exact remainder partition transports the same uniform error and
gives `|R|/n ≥ 1 - 13 theta_win - o(1)`. -/
theorem remainder_ratio_ge_main_sub_oOne
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    1 - 13 * p13Node24ThetaWindow -
        p13Node24RemainderError ctx.G.object.input.vertices.card ≤
      ((p13RemainderVertices ctx).card : ℝ) /
        ctx.G.object.input.vertices.card := by
  have nPositive : (0 : ℝ) < ctx.G.object.input.vertices.card := by
    exact_mod_cast (show 0 < ctx.G.object.input.vertices.card by omega)
  have partitionReal :
      ((p13RemainderVertices ctx).card : ℝ) + 13 * (p13 ctx : ℝ) =
        ctx.G.object.input.vertices.card := by
    exact_mod_cast p13Remainder_partition ctx
  simpa [p13Node24RemainderError] using
    remainder_ratio_lower nPositive (by norm_num) partitionReal
      (node24.theta_le_thetaWindow_add_oOne hn)

end VerifiedP13Node24FiniteDensityHandoff

/-- The paper's fractional-linear main term
`15 theta_win / (1 - 13 theta_win)`. -/
noncomputable def p13Node24TauWindow : ℝ :=
  15 * p13Node24ThetaWindow / (1 - 13 * p13Node24ThetaWindow)

theorem p13Node24TauWindow_eq_exact :
    p13Node24TauWindow = (p13WindowTauExact : ℝ) := by
  norm_num [p13Node24TauWindow, p13Node24ThetaWindow,
    p13WindowTauExact, p13WindowThetaExact,
    p13WindowDensitySkeletonNumerator, p13WindowDensityRateNumerator]

/-- Exact correction produced by transporting the density error through the
paper's fractional-linear map. -/
noncomputable def p13Node24TauError (n : Nat) : ℝ :=
  fractionalLinearError 15 13 p13Node24ThetaWindow
    (p13Node24ThetaError n)

theorem p13Node24TauError_tendsto_zero :
    Tendsto p13Node24TauError atTop (nhds 0) := by
  apply fractionalLinearError_tendsto_zero
    (scale := 15) (width := 13) (main := p13Node24ThetaWindow)
    p13Node24ThetaError_tendsto_zero
  norm_num [p13Node24ThetaWindow, p13WindowDensitySkeletonNumerator,
    p13WindowDensityRateNumerator]

/-- Because the limiting denominator is positive, the error-bearing
denominator is positive for all sufficiently large graph orders. -/
theorem p13Node24Tau_denominator_eventually_positive :
    ∀ᶠ n in atTop,
      0 < 1 - 13 * (p13Node24ThetaWindow + p13Node24ThetaError n) := by
  have shifted : Tendsto
      (fun n => p13Node24ThetaWindow + p13Node24ThetaError n) atTop
      (nhds p13Node24ThetaWindow) := by
    simpa using tendsto_const_nhds.add p13Node24ThetaError_tendsto_zero
  have denominator : Tendsto
      (fun n => 1 - 13 * (p13Node24ThetaWindow + p13Node24ThetaError n)) atTop
      (nhds (1 - 13 * p13Node24ThetaWindow)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul shifted)
  have limitPositive : 0 < 1 - 13 * p13Node24ThetaWindow := by
    norm_num [p13Node24ThetaWindow, p13WindowDensitySkeletonNumerator,
      p13WindowDensityRateNumerator]
  exact denominator.eventually (Ioi_mem_nhds limitPositive)

namespace VerifiedP13Node24FiniteDensityHandoff

/-- Pointwise fractional-linear transport once the uniform asymptotic
denominator has entered its positive tail. -/
theorem tau_le_tauWindow_add_oOne
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (hn : 5 ≤ ctx.G.object.input.vertices.card)
    (denominatorPositive :
      0 < 1 - 13 * (p13Node24ThetaWindow +
        p13Node24ThetaError ctx.G.object.input.vertices.card)) :
    15 * ((p13 ctx : ℝ) / ctx.G.object.input.vertices.card) /
        (1 - 13 * ((p13 ctx : ℝ) / ctx.G.object.input.vertices.card)) ≤
      p13Node24TauWindow +
        p13Node24TauError ctx.G.object.input.vertices.card := by
  have density := node24.theta_le_thetaWindow_add_oOne hn
  have valueNonnegative :
      0 ≤ (p13 ctx : ℝ) / ctx.G.object.input.vertices.card := by positivity
  have mainDenominatorPositive : 0 < 1 - 13 * p13Node24ThetaWindow := by
    norm_num [p13Node24ThetaWindow, p13WindowDensitySkeletonNumerator,
      p13WindowDensityRateNumerator]
  simpa [p13Node24TauWindow, p13Node24TauError] using
    fractionalLinear_le_add_error (scale := (15 : ℝ)) (width := (13 : ℝ))
      (main := p13Node24ThetaWindow)
      (error := p13Node24ThetaError ctx.G.object.input.vertices.card)
      (value := (p13 ctx : ℝ) / ctx.G.object.input.vertices.card)
      (by norm_num) (by norm_num) valueNonnegative density
      mainDenominatorPositive denominatorPositive

end VerifiedP13Node24FiniteDensityHandoff

end Erdos64EG.Internal
