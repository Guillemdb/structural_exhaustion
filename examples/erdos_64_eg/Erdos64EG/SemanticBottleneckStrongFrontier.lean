import Erdos64EG.SemanticBottleneckLocalProjection
import StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace StrongFrontier
export Graph.SurplusPatternStrongSemanticFrontier
  (required Pending classify classify_total classify_retains
    classify_obligation_exact visibleChecks visibleChecks_constant)
end StrongFrontier
end Semantic

/-!
# Node [187]: strong-semantic obligation frontier

This node consumes node [184] exactly and records the next missing theorem for
each literal projection.  Its four tags are obligations only: none supplies a
sparse exit, CT3 response, Type-B certificate, or fixed-capacity theorem.
Node [190] is the sole semantic consumer.
-/

abbrev SemanticBottleneckStrongFrontierSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :=
  Core.ExactHandoff
    (semanticBottleneckLocalProjection ctx overload homogeneous
      (semanticBottleneckLocalProjectionSource ctx overload homogeneous))

noncomputable def semanticBottleneckStrongFrontierSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckStrongFrontierSource ctx overload homogeneous :=
  Core.ExactHandoff.refl
    (semanticBottleneckLocalProjection ctx overload homogeneous
      (semanticBottleneckLocalProjectionSource ctx overload homogeneous))

structure SemanticBottleneckStrongFrontier
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    Type _ where
  pending : Semantic.StrongFrontier.Pending
    (geometricActivationStage ctx) source.output.projection
  pendingExact : pending = Semantic.StrongFrontier.classify
    (geometricActivationStage ctx) source.output.projection

noncomputable def semanticBottleneckStrongFrontier
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    SemanticBottleneckStrongFrontier ctx overload homogeneous source where
  pending := Semantic.StrongFrontier.classify
    (geometricActivationStage ctx) source.output.projection
  pendingExact := rfl

theorem semanticBottleneckStrongFrontierSource_node184_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    source.output = semanticBottleneckLocalProjection ctx overload homogeneous
      (semanticBottleneckLocalProjectionSource ctx overload homogeneous) :=
  source.outputExact

theorem semanticBottleneckStrongFrontier_pending_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    (semanticBottleneckStrongFrontier ctx overload homogeneous source).pending =
      Semantic.StrongFrontier.classify (geometricActivationStage ctx)
        source.output.projection :=
  (semanticBottleneckStrongFrontier ctx overload homogeneous source).pendingExact

theorem semanticBottleneckStrongFrontier_retains_node184
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    (semanticBottleneckStrongFrontier ctx overload homogeneous source).pending.retained =
      source.output.projection := by
  exact Semantic.StrongFrontier.classify_retains _ _

theorem semanticBottleneckStrongFrontier_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckStrongFrontierSource ctx overload homogeneous) :
    Nonempty (Semantic.StrongFrontier.Pending
      (geometricActivationStage ctx) source.output.projection) :=
  Semantic.StrongFrontier.classify_total _ _

theorem semanticBottleneckStrongFrontier_visibleChecks_constant :
    Semantic.StrongFrontier.visibleChecks ≤ 1 :=
  Semantic.StrongFrontier.visibleChecks_constant

/-- The one mathematical obligation contributed by node [187]. -/
def SemanticBottleneckStrongFrontierObligation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_residual : VerifiedSemanticBottleneckClassificationPrefix ctx) : Prop :=
  ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckStrongFrontier ctx overload homogeneous
        (semanticBottleneckStrongFrontierSource ctx overload homogeneous))

/-- Verified prefix through node [187]'s exact pending-obligation frontier. -/
abbrev VerifiedSemanticBottleneckStrongFrontierPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State
    (VerifiedSemanticBottleneckClassificationPrefix ctx)
    [SemanticBottleneckStrongFrontierObligation ctx,
      SemanticBottleneckLocalProjectionObligation ctx,
      SemanticBottleneckSwitchNormalizationObligation ctx,
      SemanticBottleneckLocalConsumerObligation ctx]

noncomputable def semanticBottleneckStrongFrontierPrefixNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SemanticBottleneckLocalProjectionObligation ctx,
        SemanticBottleneckSwitchNormalizationObligation ctx,
        SemanticBottleneckLocalConsumerObligation ctx])
      (SemanticBottleneckStrongFrontierObligation ctx) where
  prove := fun _state overload homogeneous =>
    ⟨semanticBottleneckStrongFrontier ctx overload homogeneous
      (semanticBottleneckStrongFrontierSource ctx overload homogeneous)⟩

noncomputable def verifiedSemanticBottleneckStrongFrontierPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckLocalProjectionPrefix ctx) :
    VerifiedSemanticBottleneckStrongFrontierPrefix ctx :=
  (semanticBottleneckStrongFrontierPrefixNode ctx).run previous

theorem exists_verifiedSemanticBottleneckStrongFrontierPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckStrongFrontierPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSemanticBottleneckLocalProjectionPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckStrongFrontierPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
