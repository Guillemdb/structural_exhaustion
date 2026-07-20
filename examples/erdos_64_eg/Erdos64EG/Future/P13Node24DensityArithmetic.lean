import Erdos64EG.Future.P13PartIWindowDensityTriage
import Erdos64EG.Future.P13ExactHotNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact arithmetic exported by node [24]

Node `[22]`'s corrected complementary constructor retains the actual
node-`[21]` packing and its error-bearing normalized cap.  This file records
the arithmetic consequences owned by node `[24]`.  The sharper high-entropy
cap is recorded only as a downstream requirement: the weaker window-only cap
does not imply it.

All calculations are fixed natural-number comparisons or projections from the
incoming residual.  No graph, state, context, or Boolean universe is scanned.
-/

/-- Exact rational value denoted by the manuscript's
`theta_win = 0.01270017798...`. -/
def p13WindowThetaExact : ℚ :=
  p13WindowDensitySkeletonNumerator / p13WindowDensityRateNumerator

/-- Exact rational value denoted by the manuscript's high-entropy constant
`0.01198542083...`. -/
def p13HighEntropyThetaExact : ℚ :=
  p13HighEntropySkeletonNumerator / p13HighEntropyRateNumerator

/-- Exact remainder-incidence ratio obtained from the window-only density
coefficient. -/
def p13WindowTauExact : ℚ :=
  15 * p13WindowThetaExact / (1 - 13 * p13WindowThetaExact)

/-- The printed window-only decimal is the lower eleven-decimal truncation of
the exact rational coefficient. -/
theorem p13WindowThetaExact_decimalBracket :
    (1270017798 : ℚ) / 100000000000 < p13WindowThetaExact ∧
      p13WindowThetaExact < (1270017799 : ℚ) / 100000000000 := by
  norm_num [p13WindowThetaExact, p13WindowDensitySkeletonNumerator,
    p13WindowDensityRateNumerator]

/-- The printed high-entropy decimal is the lower eleven-decimal truncation of
the exact rational coefficient. -/
theorem p13HighEntropyThetaExact_decimalBracket :
    (1198542083 : ℚ) / 100000000000 < p13HighEntropyThetaExact ∧
      p13HighEntropyThetaExact < (1198542084 : ℚ) / 100000000000 := by
  norm_num [p13HighEntropyThetaExact, p13HighEntropySkeletonNumerator,
    p13HighEntropyRateNumerator]

/-- The exact window-only incidence ratio is strictly below one quarter, as
required by the later net-charge consumer. -/
theorem p13WindowTauExact_lt_quarter :
    p13WindowTauExact < (1 : ℚ) / 4 := by
  norm_num [p13WindowTauExact, p13WindowThetaExact,
    p13WindowDensitySkeletonNumerator, p13WindowDensityRateNumerator]

/-! The repaired finite branch keeps the asymptotic correction explicit. -/

namespace VerifiedP13Node24FiniteDensityHandoff

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Exact incoming node-`[21]` provenance for the corrected, error-bearing
node-`[24]` constructor. -/
theorem predecessorExact
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    node24.previous = node21 :=
  node24.previousExact

/-- Exact sequential hot/cold accounting on the identical node-`[21]`
context.  Both normalization error and cold payment remain visible. -/
theorem sequentialHotColdAccounting
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 +
        p13WindowDensityRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale := by
  have _samePredecessor : node24.previous = node21 := node24.predecessorExact
  exact p13SequentialTotal_normalized_le_error_add_cold ctx node21

/-- The discarded-scale correction is bounded by thirty scales for every
accepted hot owner. -/
theorem sequentialScaleLossBound
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13SequentialHotScaleLoss ctx node21 ≤
      30 * (p13SequentialWeightedHotWindows ctx node21).length := by
  have _samePredecessor : node24.previous = node21 := node24.predecessorExact
  exact p13SequentialHotScaleLoss_le ctx node21

/-- The corrected finite form of `theta <= theta_win + o(1)`. -/
theorem thetaWindowCorrected
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 :=
  node24.thetaWindowWithError

/-- The corrected large-remainder handoff retains the same finite error
instead of dropping it during normalization. -/
theorem remainderCorrected
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
        ctx.G.object.input.vertices.card ≤
      p13WindowDensityRateNumerator *
          Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
          (p13RemainderVertices ctx).card +
        13 * (p13SequentialPrintedSkeletonBits ctx +
          p13SequentialHotNormalizationError ctx node21) :=
  node24.remainderWithError

/-- Error-bearing cross-multiplied precursor of the later strict-quarter
incidence comparison. -/
theorem seventyThreePackingCorrected
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale *
        (73 * p13 ctx) ≤
      73 * (p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21) :=
  node24.seventyThreePackingWithError

/-- Node `[24]` is a projection from node `[22]`'s selected constructor and
therefore performs no additional local scan. -/
def localCheckCount
    (_node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) : Nat := 0

theorem localCheckCount_polynomial
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    node24.localCheckCount ≤
      (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  simp [localCheckCount]

end VerifiedP13Node24FiniteDensityHandoff

/-- Corrected high-entropy obligation carried to the downstream two-budget
consumer.  The normalization error is retained explicitly.  This definition
names the missing proposition; it is not a proof of it. -/
def P13Node24HighEntropyDownstreamRequirement
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Prop :=
  p13HighEntropyRateNumerator * p13 ctx *
      Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
    p13HighEntropySkeletonNumerator * ctx.G.object.input.vertices.card *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale +
      p13SequentialHotNormalizationError ctx node21

end Erdos64EG.Internal
