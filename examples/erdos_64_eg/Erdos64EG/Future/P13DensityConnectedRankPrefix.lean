import Erdos64EG.Node21
import Erdos64EG.Shared.P13RemainderResidual
import Erdos64EG.Shared.CT15RemainderCurvature

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Same-context density-to-rank provenance

The standalone remainder identities and CT15 execution are meaningful before
the window-density theorem is complete, but Part IV may use them only after
node `[24]` has supplied an exact packing ceiling on the identical selected
graph.  This file records that strict dependency without manufacturing such a
ceiling or selecting a second minimal context.
-/

/-- Recover the exact CT12 packing retained inside the bounded node-`[21]`
prefix.  Every projection is a literal predecessor field. -/
def p13MultiScalePackingPrefix
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    VerifiedP13PackingPrefix ctx :=
  p13LabelAlgebraPrefix_previous ctx node21.previous.previous.residual

/-- The complete same-context prefix required before Part IV.  In particular,
`coverage` is the exact output still owed by node `[24]`; it is not inferred
from the later deficiency or rank ledgers. -/
structure P13DensityConnectedGlobalRankPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) where
  curvatureTable : VerifiedP13MultiScaleCurvaturePrefix ctx
  sameCurvatureTable : curvatureTable = node21
  remainder : VerifiedP13RemainderResidual ctx
    (p13MultiScalePackingPrefix node21) coverage
  positiveDeficiency : VerifiedP13PositiveDeficiencyPrefix ctx
  samePacking : positiveDeficiency.1 =
    p13MultiScalePackingPrefix node21
  globalRank : VerifiedP13GlobalRankClosurePrefix ctx

/-- Construct the strict prefix from node `[21]` and the genuine node-`[24]`
coverage output.  All later bookkeeping is recomputed on that same `ctx`; no
existential context or packing is reselected. -/
noncomputable def p13DensityConnectedGlobalRankPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) :
    P13DensityConnectedGlobalRankPrefix ctx node21 coverage := by
  let packing := p13MultiScalePackingPrefix node21
  let remainder := verifiedP13RemainderResidual ctx packing coverage
  let positive := verifiedP13PositiveDeficiencyPrefix ctx packing
  let curvature := verifiedP13CurvaturePrefix ctx positive
  let proper := verifiedP13ProperDelocalizationPrefix ctx curvature
  let global := verifiedP13GlobalRankClosurePrefix ctx proper
  exact {
    curvatureTable := node21
    sameCurvatureTable := rfl
    remainder := remainder
    positiveDeficiency := positive
    samePacking := rfl
    globalRank := global
  }

/-- The packing ceiling consumed downstream is exactly the one supplied by
node `[24]`. -/
theorem densityConnected_packing_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (_joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage) :
    p13 ctx ≤ coverage.windowCeiling :=
  coverage.packing_le

/-- The full-rank ledger retained for Part IV is evaluated on the same graph
and remainder as the node-`[24]` ceiling.  This theorem intentionally states
only the CT15 quotient-rank conclusion; it does not claim Boolean realization
or an entropy lower bound. -/
theorem densityConnected_fullRankCount
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage) :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  joined.globalRank.fullRankCount

end Erdos64EG.Internal
