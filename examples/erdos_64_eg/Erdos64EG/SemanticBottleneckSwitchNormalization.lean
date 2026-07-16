import Erdos64EG.SemanticBottleneckLocalConsumer
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

structure SemanticBottleneckNormalizationSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  node178 : SemanticBottleneckLocalConsumer ctx overload homogeneous
  node178Exact : node178 =
    semanticBottleneckLocalConsumer ctx overload homogeneous

noncomputable def semanticBottleneckNormalizationSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckNormalizationSource ctx overload homogeneous :=
  ⟨semanticBottleneckLocalConsumer ctx overload homogeneous, rfl⟩

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
    source.node178.previous.residual
    source.node178.frontier
  resultExact : result = Semantic.Normalization.normalize
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    source.node178.previous.residual
    source.node178.frontier

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
    source.node178.previous.residual
    source.node178.frontier
  resultExact := rfl

theorem semanticBottleneckNormalizationSource_node178_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckNormalizationSource ctx overload homogeneous) :
    source.node178 = semanticBottleneckLocalConsumer ctx overload homogeneous :=
  source.node178Exact

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
        source.node178.previous.residual source.node178.frontier :=
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
      source.node178.previous.residual source.node178.frontier) :=
  Semantic.Normalization.normalize_total _ _ _ _ _

theorem semanticBottleneckSwitchNormalization_checks_eq_zero :
    Semantic.Normalization.checks = 0 :=
  Semantic.Normalization.checks_eq_zero

/-- Verified prefix through node [181]'s exact local normalization. -/
structure VerifiedSemanticBottleneckSwitchNormalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSemanticBottleneckLocalConsumerPrefix ctx
  normalization : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckSwitchNormalization ctx overload homogeneous
        (semanticBottleneckNormalizationSource ctx overload homogeneous))

noncomputable def verifiedSemanticBottleneckSwitchNormalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckLocalConsumerPrefix ctx) :
    VerifiedSemanticBottleneckSwitchNormalizationPrefix ctx where
  previous := previous
  normalization := fun overload homogeneous =>
    ⟨semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous)⟩

theorem exists_verifiedSemanticBottleneckSwitchNormalizationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSemanticBottleneckSwitchNormalizationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSemanticBottleneckLocalConsumerPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedSemanticBottleneckSwitchNormalizationPrefix ctx previous⟩

end Erdos64EG.Internal
