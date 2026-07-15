import Erdos64EG.CT10P13LabelAlgebra
import Erdos64EG.CT9CoupledClassOverload
import StructuralExhaustion.Core.QuadraticScaleSplit

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

/-- Predecessor-linked endpoint: node `[19]` is executed only after the green
node-[18] finite label algebra on the identical selected graph. -/
structure VerifiedSurplusScaleSplitPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13LabelAlgebraPrefix ctx
  decision : ∀ windowSize remainderSize primitiveSize,
    Nonempty (SurplusScaleDecision ctx windowSize remainderSize primitiveSize)
  exactSplit : ∀ windowSize remainderSize primitiveSize,
    surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card <
          (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ∨
      (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
        surplusScaleCoefficient windowSize remainderSize primitiveSize *
          ctx.G.object.input.vertices.card
  constantWork : ∀ windowSize remainderSize primitiveSize,
    Core.QuadraticScaleSplit.checks
      (surplusScaleInput ctx windowSize remainderSize primitiveSize) = 1

noncomputable def verifiedSurplusScaleSplitPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13LabelAlgebraPrefix ctx) :
    VerifiedSurplusScaleSplitPrefix ctx where
  previous := previous
  decision := fun windowSize remainderSize primitiveSize =>
    ⟨(surplusScaleStage ctx windowSize remainderSize primitiveSize).decision⟩
  exactSplit := surplusScale_exhaustive ctx
  constantWork := fun _windowSize _remainderSize _primitiveSize => rfl

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

/-- Node `[125]`: the Part-X entry retains the entire node-[20] residual. -/
structure SparsePressureEntryResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : NonNearCubicScaleResidual ctx

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
      .sparsePressure ⟨⟨previous, windowSize, remainderSize, primitiveSize, strict⟩⟩
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
        ⟨⟨previous, windowSize, remainderSize, primitiveSize, strict⟩⟩
      exact ⟨residual, by simp [routeSurplusScale, hdecision, residual]⟩
  | bounded bound =>
      right
      let residual : BoundedSurplusScaleResidual ctx :=
        ⟨previous, windowSize, remainderSize, primitiveSize, bound⟩
      exact ⟨residual, by simp [routeSurplusScale, hdecision, residual]⟩

/-- The complete node-[19]/[20]/[125] route, still linked to node `[18]`. -/
structure VerifiedSurplusScaleRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSurplusScaleSplitPrefix ctx
  routed : ∀ (windowSize remainderSize primitiveSize : Nat),
    Nonempty (SurplusScaleRoute ctx)
  exhaustive : ∀ (windowSize remainderSize primitiveSize : Nat),
    (∃ residual : SparsePressureEntryResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .sparsePressure residual) ∨
      (∃ residual : BoundedSurplusScaleResidual ctx,
        routeSurplusScale ctx previous windowSize remainderSize primitiveSize =
          .bounded residual)
  constantWork : ∀ (windowSize remainderSize primitiveSize : Nat),
    Core.QuadraticScaleSplit.checks
      (surplusScaleInput ctx windowSize remainderSize primitiveSize) = 1

noncomputable def verifiedSurplusScaleRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx) :
    VerifiedSurplusScaleRoutingPrefix ctx where
  previous := previous
  routed := fun windowSize remainderSize primitiveSize =>
    ⟨routeSurplusScale ctx previous windowSize remainderSize primitiveSize⟩
  exhaustive := routeSurplusScale_exhaustive ctx previous
  constantWork := fun _ _ _ => rfl

theorem exists_verifiedSurplusScaleSplitPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSurplusScaleSplitPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13LabelAlgebraPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSurplusScaleSplitPrefix ctx previous⟩

theorem exists_verifiedSurplusScaleRoutingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSurplusScaleRoutingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSurplusScaleSplitPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSurplusScaleRoutingPrefix ctx previous⟩

end Erdos64EG.Internal
