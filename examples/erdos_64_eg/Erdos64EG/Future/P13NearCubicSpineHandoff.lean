import Erdos64EG.Future.SemanticBottleneckPairwiseClause
import Erdos64EG.Shared.SurplusScaleSplit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact near-cubic spine handoff at nodes [138] and [144]

The manuscript has two existing routes to the same near-cubic continuation:
the bounded side of node `[19]` (and equivalently node `[138]`'s no-overload
certificate), and the fixed-cap leaf of node `[144]`.  This file gives that
shared conclusion one exact finite type.  It introduces no diagram outcome.

The node-`[144]` record below is deliberately only an output contract.  Its
current exact predecessor retains a pending strong-semantic obligation; no
constructor is claimed until that obligation is discharged.
-/

/-- Finite pointwise form of the manuscript's near-cubic spine estimate. -/
structure P13NearCubicSpineBound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) : Prop where
  surplus_sq_le :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card

/-- The direct bounded node-`[19]` branch supplies the common spine payload
without changing its authored threshold triple. -/
def P13NearCubicSpineBound.ofBoundedSurplus
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (bounded : BoundedSurplusScaleResidual ctx) :
    P13NearCubicSpineBound ctx bounded.windowSize bounded.remainderSize
      bounded.primitiveSize :=
  ⟨bounded.bound⟩

/-- Node `[138]` supplies the identical finite spine payload on the negative
side of the exact coupled overload decision. -/
def P13NearCubicSpineBound.ofNoCoupledOverload
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat)
    (within : (coupledClassProfile ctx windowSize remainderSize primitiveSize
      ).WithinCapacity (coupledClassItems ctx)) :
    P13NearCubicSpineBound ctx windowSize remainderSize primitiveSize := by
  refine ⟨?_⟩
  simpa [surplusScaleCoefficient] using
    noCoupledOverload_quadraticSpine ctx windowSize remainderSize primitiveSize
      within

/-- The exact existing near-cubic output of node `[144]`.  The record consumes
the terminal local-separator support already computed inside node `[144]` and
must additionally carry the fixed-cap consequence.  Constructing this record
is precisely the still-open semantic bottleneck theorem; the type itself adds
no branch or edge. -/
structure P13Node144NearCubicHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Type (u + 1) extends Core.ExactHandoff
      (semanticBottleneckPairwiseClause ctx overload homogeneous
        (semanticBottleneckPairwiseClauseSource ctx overload homogeneous)) where
  spine : P13NearCubicSpineBound ctx 49 49 49

namespace P13Node144NearCubicHandoff

theorem surplus_sq_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx)}
    {homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)}
    (handoff : P13Node144NearCubicHandoff ctx overload homogeneous) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient 49 49 49 *
        ctx.G.object.input.vertices.card :=
  handoff.spine.surplus_sq_le

end P13Node144NearCubicHandoff

end Erdos64EG.Internal
