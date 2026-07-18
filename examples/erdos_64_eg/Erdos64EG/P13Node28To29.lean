import Erdos64EG.CT15RemainderCurvature
import Erdos64EG.P13NearCubicSpineHandoff
import Erdos64EG.P13Node27To28
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing edge `[28] -> [29]`

Node `[29]` is only the external-incidence supply calculation.  This adapter
indexes the reusable graph ledger by the literal node-`[28]` result and retains
the bounded-surplus certificate already carried by node `[21]`.  It does not
construct curvature coordinates or execute CT15; those belong to nodes
`[30]`--`[35]`.
-/

/-- Complete node-[29] payload on the exact node-[28] remainder. -/
structure VerifiedP13Node29ExternalIncidenceSupply
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26)
    (node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27) : Type (u + 1)
    extends Core.ExactHandoff node28 where
  deficiencyLedgerExact :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency =
      (p13RemainderDeficiencyProfile ctx).positiveDeficiency
  deficiencyFormula :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency =
      Finset.sum (p13RemainderVertices ctx) (fun vertex : ctx.G.Vertex =>
        3 - (p13RemainderCurvatureProfile ctx).internalDegree vertex)
  deficiency_le_boundaryIncidences :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      (p13RemainderCurvatureProfile ctx).boundaryIncidences
  boundaryIncidences_le_windowTokens :
    (p13RemainderCurvatureProfile ctx).boundaryIncidences ≤
      Graph.InducedPathWindowLedger.tokenCount ctx.G.object
  tokenCountExact :
    Graph.InducedPathWindowLedger.tokenCount ctx.G.object =
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object
  incidenceSupply :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object
  surplusAdjustedSupply :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object
  surplusPartition :
    Graph.InducedPathWindowLedger.windowSurplus ctx.G.object +
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object =
      Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  windowSurplus_le_total :
    Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
      Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  nearCubic : P13NearCubicSpineBound ctx
    node21.previous.windowSize node21.previous.remainderSize
      node21.previous.primitiveSize
  localWork : Graph.InducedPathWindowLedger.checks ctx.G.object ≤
    13 * ctx.G.object.input.vertices.card ^ 2

/-- Execute the manuscript's `[28] -> [29]` incidence-accounting edge. -/
noncomputable def VerifiedP13Node28PositiveDeficiency.node29
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
    (node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27) :
    VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28 where
  previous := node28
  previousExact := rfl
  deficiencyLedgerExact := p13Curvature_positiveDeficiency_eq_previous ctx
  deficiencyFormula := by
    exact node28.exactFormula
  deficiency_le_boundaryIncidences :=
    (p13RemainderCurvatureProfile ctx).positiveDeficiency_le_boundaryIncidences
      (fun vertex => ctx.baseline.trans
        (ctx.G.object.minDegree_le_degree vertex))
  boundaryIncidences_le_windowTokens :=
    Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount
      ctx.G.object
  tokenCountExact :=
    Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus
      ctx.G.object (fun vertex => ctx.baseline.trans
        (ctx.G.object.minDegree_le_degree vertex))
  incidenceSupply :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  surplusAdjustedSupply := p13Remainder_surplusAdjustedDeficiency ctx
  surplusPartition :=
    Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus
      ctx.G.object
  windowSurplus_le_total := by
    have partition :=
      Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus
        ctx.G.object
    omega
  nearCubic := P13NearCubicSpineBound.ofBoundedSurplus node21.previous
  localWork :=
    Graph.InducedPathWindowLedger.checks_le_thirteen_mul_square ctx.G.object

end Erdos64EG.Internal
