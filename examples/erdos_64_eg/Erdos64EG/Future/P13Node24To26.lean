import Erdos64EG.Future.P13Node24AsymptoticTransport
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-! Exact existing-edge handoff `[24] -> [25] -> [26]`. -/

structure VerifiedP13Node25LargeRemainder
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    extends Core.ExactHandoff node24 where
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  coverageExact : coverage = p13ExactPackingCoverage ctx node21
  remainder : VerifiedP13RemainderResidual ctx
    (p13MultiScalePackingPrefix node21) coverage

noncomputable def VerifiedP13Node24FiniteDensityHandoff.node25
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    VerifiedP13Node25LargeRemainder ctx node21 node24 := by
  let coverage := p13ExactPackingCoverage ctx node21
  exact {
    previous := node24
    previousExact := rfl
    coverage := coverage
    coverageExact := rfl
    remainder := verifiedP13RemainderResidual ctx
      (p13MultiScalePackingPrefix node21) coverage
  }

theorem VerifiedP13Node25LargeRemainder.large
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    (node25 : VerifiedP13Node25LargeRemainder ctx node21 node24) :
    node25.coverage.remainderFloor ≤ (p13RemainderVertices ctx).card :=
  node25.remainder.large

abbrev VerifiedP13Node26RemainderContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :=
  VerifiedP13Node25LargeRemainder ctx node21 node24

def VerifiedP13Node25LargeRemainder.node26
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    (node25 : VerifiedP13Node25LargeRemainder ctx node21 node24) :
    VerifiedP13Node26RemainderContinuation ctx node21 node24 := node25

/-! ## Existing edge `[26] -> [27]` -/

/-- Complete node-[27] payload on the literal node-[26] remainder.

The two formulations are retained together: `InternalMinDegreeFree` is the
induced-support form consumed by the graph profiles, while
`HasInternalSubgraphMinDegreeAtLeast` is the manuscript's arbitrary finite
subgraph formulation.  This structure introduces no new branch and selects no
new graph object. -/
structure VerifiedP13Node27NoInternalThreeCore
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    extends Core.ExactHandoff node26 where
  noInternalThreeCore : (p13Remainder ctx).InternalMinDegreeFree 3
  noInternalSubgraphThreeCore :
    ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3

/-- Execute the manuscript's existing `[26] -> [27]` handoff without another
graph scan.  Both conclusions are inherited from the exact remainder stored by
node [26]. -/
def VerifiedP13Node25LargeRemainder.node27
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24) :
    VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26 where
  previous := node26
  previousExact := rfl
  noInternalThreeCore := node26.remainder.noInternalThreeCore
  noInternalSubgraphThreeCore :=
    node26.remainder.noInternalSubgraphThreeCore

/-- Node [27] performs only proof-field projection from node [26]. -/
def p13Node27LocalChecks : Nat := 0

theorem p13Node27LocalChecks_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node27LocalChecks ≤ (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  simp [p13Node27LocalChecks]

/-- The retained nonempty P13 packing forces at least thirteen ambient
vertices, discharging the finite asymptotic transport side condition. -/
theorem VerifiedP13Node25LargeRemainder.thirteen_le_order
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    (_node25 : VerifiedP13Node25LargeRemainder ctx node21 node24) :
    13 ≤ ctx.G.object.input.vertices.card := by
  have windowsNonempty := p13PackingPrefix_nonempty ctx
    (p13MultiScalePackingPrefix node21)
  have packingPositive : 0 < p13 ctx := by
    have lengthPositive : 0 < (p13Windows ctx).length := by
      apply Nat.pos_of_ne_zero
      intro lengthZero
      apply windowsNonempty
      exact List.length_eq_zero_iff.mp lengthZero
    simpa [p13Windows, p13, Graph.InducedPathPacking.windows,
      Graph.InducedPathPacking.packingNumber] using lengthPositive
  have partition := p13Remainder_partition ctx
  omega

theorem VerifiedP13Node25LargeRemainder.ratio_ge_main_sub_oOne
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    (node25 : VerifiedP13Node25LargeRemainder ctx node21 node24) :
    1 - 13 * p13Node24ThetaWindow -
        p13Node24RemainderError ctx.G.object.input.vertices.card ≤
      ((p13RemainderVertices ctx).card : ℝ) /
        ctx.G.object.input.vertices.card :=
  node24.remainder_ratio_ge_main_sub_oOne (by
    have := node25.thirteen_le_order
    omega)

def p13Node24To26LocalChecks : Nat := 0

theorem p13Node24To26LocalChecks_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node24To26LocalChecks ≤ (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  simp [p13Node24To26LocalChecks]

end Erdos64EG.Internal
