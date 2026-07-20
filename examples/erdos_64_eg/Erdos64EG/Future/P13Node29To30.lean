import Erdos64EG.Future.P13Node28To29
import Erdos64EG.Shared.P13Node30Constants
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing edge `[29] -> [30]`

Node `[30]` is the degree-count wedge floor.  The graph theorem is valid for
every supplied finite support, hence in particular for each remainder
component.  The aggregate remainder estimate consumes the exact node-`[29]`
deficiency supply.  No curvature coordinate or CT15 rank is constructed here.
-/

/-- The exact window-only wedge coefficient from the manuscript. -/
noncomputable def p13Node30OmegaWindow : ℝ :=
  3 - 2 * p13Node24TauWindow

theorem p13Node30OmegaWindow_gt_printed :
    (254365026308 / 100000000000 : ℝ) < p13Node30OmegaWindow := by
  norm_num [p13Node30OmegaWindow, p13Node24TauWindow,
    p13Node24ThetaWindow, p13WindowDensitySkeletonNumerator,
    p13WindowDensityRateNumerator,
    Core.DensityAsymptoticTransport.fractionalLinearError]

/-- Complete node-[30] payload indexed by the literal node-[29] output. -/
structure VerifiedP13Node30WedgeLower
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26)
    (node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27)
    (node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28) : Type (u + 3)
    extends Core.ExactHandoff node29 where
  componentWedgeFloor : ∀ component : Finset ctx.G.Vertex,
    let profile : Graph.PositiveDeficiencyWedge.Profile ctx.G.object :=
      { core := component }
    3 * component.card - 2 * profile.positiveDeficiency ≤
      profile.wedgeCount
  remainderWedgeFloor :
    3 * (p13RemainderVertices ctx).card -
        2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount
  windowFiniteSupply :
    3 * (p13RemainderVertices ctx).card ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        2 * Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  rateTransport : ∀ (rate error : ℝ),
    ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
        rate * (p13RemainderVertices ctx).card + error →
      (3 - 2 * rate) * (p13RemainderVertices ctx).card ≤
        (p13RemainderCurvatureProfile ctx).wedgeCount + 2 * error
  highEntropyTransport : ∀ error : ℝ,
    ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
        p13Node30HighEntropyDeficiencyRate *
          (p13RemainderVertices ctx).card + error →
      p13Node30OmegaHighEntropy * (p13RemainderVertices ctx).card ≤
        (p13RemainderCurvatureProfile ctx).wedgeCount + 2 * error
  nearCubic : P13NearCubicSpineBound ctx
    node21.previous.windowSize node21.previous.remainderSize
      node21.previous.primitiveSize
  localWork : (p13RemainderCurvatureProfile ctx).checks ≤
    ctx.G.object.input.vertices.card ^ 2

/-- Execute the manuscript's `[29] -> [30]` wedge-floor edge. -/
noncomputable def VerifiedP13Node29ExternalIncidenceSupply.node30
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
    {node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27}
    (node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28) :
    VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29 where
  previous := node29
  previousExact := rfl
  componentWedgeFloor := by
    intro component
    exact (show Graph.PositiveDeficiencyWedge.Profile ctx.G.object from
      { core := component }).wedgeFloor
  remainderWedgeFloor := p13Remainder_wedgeFloor ctx
  windowFiniteSupply := by
    have wedge :=
      (p13RemainderCurvatureProfile ctx).three_mul_card_le_wedgeCount_add_twice_deficiency
    change 3 * (p13RemainderVertices ctx).card ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount +
        2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency at wedge
    have deficiency :
        (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
          15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
      node29.incidenceSupply.trans (Nat.add_le_add_left
        node29.windowSurplus_le_total _)
    have twice := Nat.mul_le_mul_left 2 deficiency
    omega
  rateTransport := by
    intro rate error deficiency
    exact (p13RemainderCurvatureProfile ctx).wedgeRate_of_deficiencyRate
      rate error deficiency
  highEntropyTransport := by
    intro error deficiency
    rw [p13Node30OmegaHighEntropy_eq]
    exact (p13RemainderCurvatureProfile ctx).wedgeRate_of_deficiencyRate
      p13Node30HighEntropyDeficiencyRate error deficiency
  nearCubic := node29.nearCubic
  localWork := (p13RemainderCurvatureProfile ctx).checks_le_square

end Erdos64EG.Internal
