import Erdos64EG.CT10P13LabelAlgebra
import Erdos64EG.CT9CoupledClassOverload
import StructuralExhaustion.Core.QuadraticScaleSplit
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact non-near-cubic scale decision

Diagram node `[19]` compares the actual degree surplus with a fixed
square-root scale.  The implementation uses the equivalent squared natural
inequality.  Its coefficient is the same explicit homogeneous-cap coefficient
used by node `[138]`, parameterized by the three authored local pattern sizes;
there is no floating-point square root and no global enumeration.
-/

def surplusScaleCoefficient
    (windowSize remainderSize primitiveSize : Nat) : Nat :=
  450 * Graph.SurplusClasswiseOverload.maxCap
    windowSize remainderSize primitiveSize + 1

noncomputable def surplusScaleInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :
    Core.QuadraticScaleSplit.Input where
  load := Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  coefficient := surplusScaleCoefficient windowSize remainderSize primitiveSize
  order := ctx.G.object.input.vertices.card

abbrev SurplusScaleDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :=
  Core.QuadraticScaleSplit.Decision
    (surplusScaleInput ctx windowSize remainderSize primitiveSize)

/-- Constant-work execution of node `[19]`. -/
noncomputable def surplusScaleStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :=
  Core.QuadraticScaleSplit.verifiedStage
    (surplusScaleInput ctx windowSize remainderSize primitiveSize)

theorem surplusScale_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :
    surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card <
          (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ∨
      (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
        surplusScaleCoefficient windowSize remainderSize primitiveSize *
          ctx.G.object.input.vertices.card :=
  (surplusScaleStage ctx windowSize remainderSize primitiveSize).total

/-- The three local obligations contributed by the exact node-[19] split. -/
def SurplusScaleDecisionAvailable
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedP13LabelAlgebraPrefix ctx) : Prop :=
  ∀ windowSize remainderSize primitiveSize,
    Nonempty (SurplusScaleDecision ctx windowSize remainderSize primitiveSize)

def SurplusScaleExactSplit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedP13LabelAlgebraPrefix ctx) : Prop :=
  ∀ windowSize remainderSize primitiveSize,
    surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card <
          (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ∨
      (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
        surplusScaleCoefficient windowSize remainderSize primitiveSize *
          ctx.G.object.input.vertices.card

def SurplusScaleConstantWork
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedP13LabelAlgebraPrefix ctx) : Prop :=
  ∀ windowSize remainderSize primitiveSize,
    Core.QuadraticScaleSplit.checks
      (surplusScaleInput ctx windowSize remainderSize primitiveSize) = 1

/-- Predecessor-linked endpoint: node `[19]` is executed only after the green
node-[18] finite label algebra on the identical selected graph.  The framework
retains that literal predecessor and accumulates the node's three obligations. -/
abbrev VerifiedSurplusScaleSplitPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State (VerifiedP13LabelAlgebraPrefix ctx)
    [SurplusScaleConstantWork ctx, SurplusScaleExactSplit ctx,
      SurplusScaleDecisionAvailable ctx]

noncomputable def surplusScaleDecisionNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node (facts := [])
      (SurplusScaleDecisionAvailable ctx) where
  prove := fun _state windowSize remainderSize primitiveSize =>
    ⟨(surplusScaleStage ctx windowSize remainderSize primitiveSize).decision⟩

noncomputable def surplusScaleExactSplitNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SurplusScaleDecisionAvailable ctx])
      (SurplusScaleExactSplit ctx) where
  prove := fun _state => surplusScale_exhaustive ctx

noncomputable def surplusScaleConstantWorkNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SurplusScaleExactSplit ctx,
        SurplusScaleDecisionAvailable ctx])
      (SurplusScaleConstantWork ctx) where
  prove := fun _state _windowSize _remainderSize _primitiveSize => rfl

noncomputable def verifiedSurplusScaleSplitPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13LabelAlgebraPrefix ctx) :
    VerifiedSurplusScaleSplitPrefix ctx :=
  (surplusScaleConstantWorkNode ctx).run
    ((surplusScaleExactSplitNode ctx).run
      ((surplusScaleDecisionNode ctx).run
        (Core.ResidualRefinement.State.initial previous)))

/-!
## Typed continuation of the scale split

The decision at node `[19]` is consumed at fixed authored local sizes.  The
strict outcome is node `[20]` and is carried unchanged into the Part-X entry
at node `[125]`; the complementary outcome is the bounded-surplus input of
node `[21]`.  These structures contain the literal predecessor and inequality,
so neither continuation can be constructed from an unrelated graph or from a
weaker numerical statement.
-/

/-- Node `[20]`: the strict, non-near-cubic outcome of the exact node-[19]
comparison at the selected local sizes. -/
structure NonNearCubicScaleResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : VerifiedSurplusScaleSplitPrefix ctx
  windowSize : Nat
  remainderSize : Nat
  primitiveSize : Nat
  strict : surplusScaleCoefficient windowSize remainderSize primitiveSize *
      ctx.G.object.input.vertices.card <
        (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2

/-- Node `[125]`: the Part-X entry retains the entire node-[20] residual via
the framework's exact zero-copy handoff. -/
abbrev SparsePressureEntryResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Σ previous : NonNearCubicScaleResidual ctx, Core.ExactHandoff previous

/-- Complementary bounded-surplus residual consumed by node `[21]`. -/
structure BoundedSurplusScaleResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : VerifiedSurplusScaleSplitPrefix ctx
  windowSize : Nat
  remainderSize : Nat
  primitiveSize : Nat
  bound : (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card

/-- Exact typed routing of the exhaustive node-[19] decision. -/
inductive SurplusScaleRoute
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
  | sparsePressure : SparsePressureEntryResidual ctx → SurplusScaleRoute ctx
  | bounded : BoundedSurplusScaleResidual ctx → SurplusScaleRoute ctx

/-- Execute the node-[19] decision and package exactly one legal continuation.
The operation performs the same single comparison as `surplusScaleStage`. -/
noncomputable def routeSurplusScale
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx)
    (windowSize remainderSize primitiveSize : Nat) :
    SurplusScaleRoute ctx :=
  match (surplusScaleStage ctx windowSize remainderSize primitiveSize).decision with
  | .large strict =>
      let residual : NonNearCubicScaleResidual ctx :=
        ⟨previous, windowSize, remainderSize, primitiveSize, strict⟩
      .sparsePressure ⟨residual, Core.ExactHandoff.refl residual⟩
  | .bounded bound =>
      .bounded ⟨previous, windowSize, remainderSize, primitiveSize, bound⟩

theorem routeSurplusScale_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx)
    (windowSize remainderSize primitiveSize : Nat) :
    (∃ residual : SparsePressureEntryResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .sparsePressure residual) ∨
      (∃ residual : BoundedSurplusScaleResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .bounded residual) := by
  generalize hdecision :
    (surplusScaleStage ctx windowSize remainderSize primitiveSize).decision =
      decision
  cases decision with
  | large strict =>
      left
      let residual : SparsePressureEntryResidual ctx :=
        let node20 : NonNearCubicScaleResidual ctx :=
          ⟨previous, windowSize, remainderSize, primitiveSize, strict⟩
        ⟨node20, Core.ExactHandoff.refl node20⟩
      exact ⟨residual, by simp [routeSurplusScale, hdecision, residual]⟩
  | bounded bound =>
      right
      let residual : BoundedSurplusScaleResidual ctx :=
        ⟨previous, windowSize, remainderSize, primitiveSize, bound⟩
      exact ⟨residual, by simp [routeSurplusScale, hdecision, residual]⟩

/-- The three local obligations contributed by routing node `[19]`. -/
def SurplusScaleRouted
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedSurplusScaleSplitPrefix ctx) : Prop :=
  ∀ (_windowSize _remainderSize _primitiveSize : Nat),
    Nonempty (SurplusScaleRoute ctx)

def SurplusScaleRouteExhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx) : Prop :=
  ∀ (windowSize remainderSize primitiveSize : Nat),
    (∃ residual : SparsePressureEntryResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .sparsePressure residual) ∨
      (∃ residual : BoundedSurplusScaleResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .bounded residual)

def SurplusScaleRouteConstantWork
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedSurplusScaleSplitPrefix ctx) : Prop :=
  ∀ (windowSize remainderSize primitiveSize : Nat),
    Core.QuadraticScaleSplit.checks
      (surplusScaleInput ctx windowSize remainderSize primitiveSize) = 1

/-- The complete node-[19]/[20]/[125] route, still linked to node `[18]`. -/
abbrev VerifiedSurplusScaleRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State (VerifiedSurplusScaleSplitPrefix ctx)
    [SurplusScaleRouteConstantWork ctx, SurplusScaleRouteExhaustive ctx,
      SurplusScaleRouted ctx]

noncomputable def surplusScaleRoutedNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node (facts := [])
      (SurplusScaleRouted ctx) where
  prove := fun state windowSize remainderSize primitiveSize =>
    ⟨routeSurplusScale ctx state.residual windowSize remainderSize primitiveSize⟩

noncomputable def surplusScaleRouteExhaustiveNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SurplusScaleRouted ctx])
      (SurplusScaleRouteExhaustive ctx) where
  prove := fun state => routeSurplusScale_exhaustive ctx state.residual

noncomputable def surplusScaleRouteConstantWorkNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SurplusScaleRouteExhaustive ctx, SurplusScaleRouted ctx])
      (SurplusScaleRouteConstantWork ctx) where
  prove := fun _state _ _ _ => rfl

noncomputable def verifiedSurplusScaleRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx) :
    VerifiedSurplusScaleRoutingPrefix ctx :=
  (surplusScaleRouteConstantWorkNode ctx).run
    ((surplusScaleRouteExhaustiveNode ctx).run
      ((surplusScaleRoutedNode ctx).run
        (Core.ResidualRefinement.State.initial previous)))

theorem exists_verifiedSurplusScaleSplitPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSurplusScaleSplitPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedP13LabelAlgebraPrefix object baseline avoids
  exact ⟨ctx, verifiedSurplusScaleSplitPrefix ctx previous, rankLe⟩

theorem exists_verifiedSurplusScaleRoutingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSurplusScaleRoutingPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSurplusScaleSplitPrefix object baseline avoids
  exact ⟨ctx, verifiedSurplusScaleRoutingPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
