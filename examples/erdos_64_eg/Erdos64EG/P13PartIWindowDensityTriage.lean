import Erdos64EG.P13ClosureRobustPartIV

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact Part-I window-density triage

This file exposes the three arithmetic leaves immediately below the verified
node-`[21]` prefix.  It does not infer the still-open node-`[24]` density
theorem from the 91-row curvature table.  Instead, it fixes the actual packing
as the ceiling and decides the two exact finite predicates required by the
typed node-`[24]` boundary.

The positive leaf is a genuine `VerifiedP13WindowDensityOutput`.  Each
negative leaf retains the same node-`[21]` predecessor and the exact failed
inequality.  Consequently a later cold-skeleton proof cannot silently replace
an obstruction by an assumed density certificate.  The decision performs two
natural-number comparisons and enumerates no vertices, graphs, states,
contexts, or Boolean assignments.
-/

/-- The canonical coverage datum uses the actual CT12 packing number.  This is
bookkeeping only: it does not assert the numerical density cap. -/
noncomputable def p13ExactPackingCoverage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13CoverageResidual ctx (p13MultiScalePackingPrefix node21) where
  windowCeiling := p13 ctx
  packing_le := le_rfl

/-- Exact exhaustive routing boundary below node `[21]`.

* `certified` contains all fields required by node `[24]`;
* `densityOverflow` is the literal failure of the printed finite density cap;
* `quarterObstruction` retains the density cap but records failure of the
  strict quarter-budget inequality.
-/
inductive P13PartIWindowDensityOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  | certified
      (output : VerifiedP13WindowDensityOutput ctx node21)
  | densityOverflow
      (coverage : P13CoverageResidual ctx
        (p13MultiScalePackingPrefix node21))
      (failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling)
  | quarterObstruction
      (coverage : P13CoverageResidual ctx
        (p13MultiScalePackingPrefix node21))
      (densityCap : P13WindowDensityFiniteCap ctx coverage.windowCeiling)
      (failedQuarter :
        ¬P13QuarterNetBudget ctx (node21 := node21) coverage)

/-- Execute the exact two-comparison trichotomy. -/
noncomputable def runP13PartIWindowDensityTriage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13PartIWindowDensityOutcome ctx node21 := by
  let coverage := p13ExactPackingCoverage ctx node21
  by_cases densityCap :
      P13WindowDensityFiniteCap ctx coverage.windowCeiling
  · by_cases quarter :
        P13QuarterNetBudget ctx (node21 := node21) coverage
    · exact .certified ⟨⟨coverage, densityCap, quarter⟩⟩
    · exact .quarterObstruction coverage densityCap quarter
  · exact .densityOverflow coverage densityCap

/-- The overflow leaf is the strict reverse of the finite density cap. -/
theorem P13PartIWindowDensityOutcome.densityOverflow_strict
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling) :
    p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card <
      p13WindowDensityRateNumerator * coverage.windowCeiling := by
  exact Nat.lt_of_not_ge failedCap

/-- The quarter-obstruction leaf is the non-strict reverse of the strict
quarter-budget inequality. -/
theorem P13PartIWindowDensityOutcome.quarterObstruction_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (failedQuarter :
      ¬P13QuarterNetBudget ctx (node21 := node21) coverage) :
    coverage.remainderFloor ≤
      4 * p13CoverageNetBudgetUpper ctx (node21 := node21) coverage := by
  exact Nat.le_of_not_gt failedQuarter

/-- Every certified leaf composes through the already verified Part-IV
strict-quarter handoff without any Boolean-product premise. -/
noncomputable def P13PartIWindowDensityOutcome.certifiedHandoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (output : VerifiedP13WindowDensityOutput ctx node21) :
    P13QuarterNetDeficiencyHandoff ctx node21 output.coverage :=
  p13ClosureRobustPartIV output

end Erdos64EG.Internal
