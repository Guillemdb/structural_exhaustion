import Erdos64EG.Shared.CT14P13PositiveDeficiency
import Erdos64EG.Future.P13Node24To26
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing edge `[27] -> [28]`

The reusable graph-accounting payload predates the exact Part-I/Part-II
handoff.  This thin dependent adapter indexes that payload by the literal
node-[27] result; it adds no mathematical case and performs no search.
-/

/-- Complete node-[28] payload indexed by the literal node-[27] output. -/
structure VerifiedP13Node28PositiveDeficiency
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26) :
    Type (u + 3) extends Core.ExactHandoff node27 where
  accounting : VerifiedP13PositiveDeficiencyPrefix ctx
  exactFormula :
    (p13RemainderDeficiencyProfile ctx).positiveDeficiency =
      Finset.sum (p13RemainderVertices ctx) (fun vertex : ctx.G.Vertex =>
        3 - (p13RemainderDeficiencyProfile ctx).internalDegree vertex)
  noInternalThreeCore : (p13Remainder ctx).InternalMinDegreeFree 3

/-- Execute node [28] on the exact node-[27] remainder. -/
noncomputable def VerifiedP13Node27NoInternalThreeCore.node28
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26) :
    VerifiedP13Node28PositiveDeficiency ctx node21 node24 node26 node27 where
  previous := node27
  previousExact := rfl
  accounting := verifiedP13PositiveDeficiencyPrefix ctx
    node27.previous.remainder.packing
  exactFormula := p13Remainder_positiveDeficiency_eq ctx
  noInternalThreeCore := node27.noInternalThreeCore

/-- One induced-neighbour scan for each literal remainder vertex. -/
noncomputable def p13Node28LocalChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  (p13RemainderVertices ctx).card * ctx.G.object.input.vertices.card

theorem p13Node28LocalChecks_le_square
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node28LocalChecks ctx ≤ ctx.G.object.input.vertices.card ^ 2 := by
  have remainder_le :
      (p13RemainderVertices ctx).card ≤ ctx.G.object.input.vertices.card := by
    have partition := p13Remainder_partition ctx
    omega
  simpa [p13Node28LocalChecks, pow_two] using
    Nat.mul_le_mul_right ctx.G.object.input.vertices.card remainder_le

end Erdos64EG.Internal
