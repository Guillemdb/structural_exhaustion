import Erdos64EG.Future.P13Node148LiveHotDecision
import Erdos64EG.Future.P13Node24DensityArithmetic
import StructuralExhaustion.Core.WorkBudget

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [149]: corrected finite P13 density cap

This terminal node consumes the exact yes payload selected at node `[148]`.
It retains that particular dependent predecessor and exports the corrected
finite density inequality.  The uniform normalization producer converts its
literal natural-number correction into the manuscript's `o(n log n)` term,
including both binary-log rounding and discarded-scale loss.
-/

/-- The printed window-density coefficient, represented in the real field
used by the asymptotic conclusion. -/
noncomputable def p13Node149ThetaWindow : ℝ :=
  (p13WindowDensitySkeletonNumerator : ℝ) /
    p13WindowDensityRateNumerator

theorem p13Node149ThetaWindow_eq_exact :
    p13Node149ThetaWindow = (p13WindowThetaExact : ℝ) := by
  norm_num [p13Node149ThetaWindow, p13WindowThetaExact,
    p13WindowDensitySkeletonNumerator, p13WindowDensityRateNumerator]

/-- The explicit `o(1)` term obtained by dividing the uniform normalization
envelope by the exact finite binary-log budget. -/
noncomputable def p13Node149ThetaError (n : Nat) : ℝ :=
  (1 / ((p13WindowDensityRateNumerator : ℝ) *
      (p13ExactHotCertificateScale : ℝ))) *
    (p13SequentialHotNormalizationRealEnvelope n /
      ((n : ℝ) * (Nat.log 2 n : ℝ)))

/-- The additive term in the normalized node-[149] conclusion tends to zero
uniformly with graph order. -/
theorem p13Node149ThetaError_tendsto_zero :
    Filter.Tendsto p13Node149ThetaError Filter.atTop (nhds 0) := by
  have normalized :=
    Core.BinaryLogNormalization.tendsto_div_natCast_mul_natLog_two_nhds_zero
      p13SequentialHotNormalizationRealEnvelope
      p13SequentialHotNormalizationRealEnvelope_isLittleO
  unfold p13Node149ThetaError
  simpa using (tendsto_const_nhds.mul normalized)

/-- The exact terminal certificate at node `[149]`, indexed by both immediate
dependent predecessors. -/
structure VerifiedP13Node149DensityCap
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21)
    (_node148Yes : P13Node148To149 ctx node21 node146No) : Type (u + 3) where
  correctedHandoff : VerifiedP13Node24FiniteDensityHandoff ctx node21

noncomputable def verifiedP13Node149DensityCap
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148Yes : P13Node148To149 ctx node21 node146No) :
    VerifiedP13Node149DensityCap ctx node21 node146No node148Yes where
  correctedHandoff := ⟨⟨node21, rfl⟩, node148Yes.densityCap⟩

namespace VerifiedP13Node149DensityCap

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  {node146No : P13Node146To148 ctx node21}
  {node148Yes : P13Node148To149 ctx node21 node146No}

/-- The complete error-bearing cross-multiplied density conclusion. -/
theorem correctedThetaCap
    (node149 : VerifiedP13Node149DensityCap ctx node21 node146No node148Yes) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 := by
  exact node149.correctedHandoff.thetaWindowCorrected

/-- Original node-[149] terminal conclusion in normalized form.  The error
term is the single uniform `o(1)` sequence proved above, rather than a
pointwise or graph-family assumption. -/
theorem theta_le_thetaWindow_add_oOne
    (node149 : VerifiedP13Node149DensityCap ctx node21 node146No node148Yes)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13 ctx : ℝ) / ctx.G.object.input.vertices.card ≤
      p13Node149ThetaWindow +
        p13Node149ThetaError ctx.G.object.input.vertices.card := by
  let n := ctx.G.object.input.vertices.card
  let logN := Nat.log 2 n
  have nPositive : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have logNPositiveNat : 0 < logN :=
    Nat.log_pos (show 1 < 2 by omega) (show 2 ≤ n by omega)
  have logNPositive : (0 : ℝ) < logN := by exact_mod_cast logNPositiveNat
  have ratePositive : (0 : ℝ) < p13WindowDensityRateNumerator := by
    norm_num [p13WindowDensityRateNumerator]
  have scalePositive : (0 : ℝ) < p13ExactHotCertificateScale := by
    unfold p13ExactHotCertificateScale
    positivity
  have capNat := node149.correctedThetaCap
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
  simpa [p13Node149ThetaWindow, p13Node149ThetaError, n, logN] using normalized

/-- The same terminal certificate exposes the corrected large-remainder
arithmetic required by later remainder bookkeeping without dropping error. -/
theorem correctedRemainderCap
    (node149 : VerifiedP13Node149DensityCap ctx node21 node146No node148Yes) :
    p13WindowDensityRateNumerator *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
        ctx.G.object.input.vertices.card ≤
      p13WindowDensityRateNumerator *
          Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
          (p13RemainderVertices ctx).card +
        13 * (p13SequentialPrintedSkeletonBits ctx +
          p13SequentialHotNormalizationError ctx node21) := by
  exact node149.correctedHandoff.remainderCorrected

/-- Node `[149]` is a terminal projection and performs no additional local
checks after node `[148]` has selected the yes edge. -/
def localCheckCount
    (_node149 : VerifiedP13Node149DensityCap ctx node21 node146No node148Yes) :
    Nat := 0

theorem localCheckCount_polynomial
    (node149 : VerifiedP13Node149DensityCap ctx node21 node146No node148Yes) :
    node149.localCheckCount ≤
      (ctx.G.object.input.vertices.card + 1) ^ 1 := by
  simp [localCheckCount]

end VerifiedP13Node149DensityCap

abbrev P13Node149RefinementStage
    (residual : P13Node145RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node148To149Stage
    (fun residual node148 => VerifiedP13Node149DensityCap residual.ctx
      residual.node21 node148.previous node148.output) residual

noncomputable def p13Node149Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node148To149Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node149RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node148 =>
      verifiedP13Node149DensityCap node148.output)

end Erdos64EG.Internal
