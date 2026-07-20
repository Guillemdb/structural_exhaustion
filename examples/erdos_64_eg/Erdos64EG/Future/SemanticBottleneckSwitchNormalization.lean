import Erdos64EG.Future.SemanticBottleneckLocalConsumer
import StructuralExhaustion.Graph.SurplusPatternSemanticNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace Normalization
export Graph.SurplusPatternSemanticNormalization
  (Result normalize normalize_total checks checks_eq_zero)
end Normalization
end Semantic

/-!
# Node [181]: cubic-switch / high-separator normalization

The node consumes the exact integrated node-[178] result.  Cubic branches
become literal four-vertex `CubicStar.Data`; high branches keep their degree
lower bound; mismatch and prefix branches remain unchanged.  The advertised
semantic exits are deliberately not claimed.
-/

abbrev SemanticBottleneckNormalizationSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :=
  Core.ExactHandoff (semanticBottleneckLocalConsumer ctx overload homogeneous)

noncomputable def semanticBottleneckNormalizationSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckNormalizationSource ctx overload homogeneous :=
  Core.ExactHandoff.refl
    (semanticBottleneckLocalConsumer ctx overload homogeneous)

structure SemanticBottleneckSwitchNormalization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) : Type u where
  result : Semantic.Normalization.Result
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    source.output.previous.residual
    source.output.frontier
  resultExact : result = Semantic.Normalization.normalize
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    source.output.previous.residual
    source.output.frontier

noncomputable def semanticBottleneckSwitchNormalization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) :
    SemanticBottleneckSwitchNormalization ctx overload homogeneous source where
  result := Semantic.Normalization.normalize
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    source.output.previous.residual
    source.output.frontier
  resultExact := rfl

theorem semanticBottleneckNormalizationSource_node178_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) :
    source.output = semanticBottleneckLocalConsumer ctx overload homogeneous :=
  source.outputExact

theorem semanticBottleneckSwitchNormalization_result_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) :
    (semanticBottleneckSwitchNormalization ctx overload homogeneous source).result =
      Semantic.Normalization.normalize (geometricActivationStage ctx)
        (canonicalGeometricPredecessor ctx overload homogeneous).collision
        (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
        source.output.previous.residual source.output.frontier :=
  (semanticBottleneckSwitchNormalization ctx overload homogeneous source).resultExact

theorem semanticBottleneckSwitchNormalization_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) :
    Nonempty (Semantic.Normalization.Result
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
      source.output.previous.residual source.output.frontier) :=
  Semantic.Normalization.normalize_total _ _ _ _ _

theorem semanticBottleneckSwitchNormalization_checks_eq_zero :
    Semantic.Normalization.checks = 0 :=
  Semantic.Normalization.checks_eq_zero

/-- The one mathematical obligation contributed by node [181]. -/
def SemanticBottleneckSwitchNormalizationObligation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_residual : VerifiedSemanticBottleneckClassificationPrefix ctx) : Prop :=
  ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckSwitchNormalization ctx overload homogeneous
        (semanticBottleneckNormalizationSource ctx overload homogeneous))

/-- Verified prefix through node [181]'s exact local normalization. -/
abbrev VerifiedSemanticBottleneckSwitchNormalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State
    (VerifiedSemanticBottleneckClassificationPrefix ctx)
    [SemanticBottleneckSwitchNormalizationObligation ctx,
      SemanticBottleneckLocalConsumerObligation ctx]

noncomputable def semanticBottleneckSwitchNormalizationPrefixNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SemanticBottleneckLocalConsumerObligation ctx])
      (SemanticBottleneckSwitchNormalizationObligation ctx) where
  prove := fun _state overload homogeneous =>
    ⟨semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous)⟩

noncomputable def verifiedSemanticBottleneckSwitchNormalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckLocalConsumerPrefix ctx) :
    VerifiedSemanticBottleneckSwitchNormalizationPrefix ctx :=
  (semanticBottleneckSwitchNormalizationPrefixNode ctx).run previous

theorem exists_verifiedSemanticBottleneckSwitchNormalizationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckSwitchNormalizationPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSemanticBottleneckLocalConsumerPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckSwitchNormalizationPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
