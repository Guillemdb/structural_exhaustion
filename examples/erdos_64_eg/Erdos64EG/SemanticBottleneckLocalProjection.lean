import Erdos64EG.SemanticBottleneckSwitchNormalization
import StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace LocalProjection
export Graph.SurplusPatternSemanticLocalProjection
  (Projection project project_total visibleChecks visibleChecks_linear)
end LocalProjection
end Semantic

/-!
# Node [184]: literal separator projection

This node consumes node [181] exactly.  Cubic leaves expose the literal
three-boundary switch already contained in `CubicStar.Data`; high leaves expose
only the selected centre's declared incident-port schedule.  All other leaves
are preserved, and no response, target, quotient, or capacity semantics are
introduced.
-/

abbrev SemanticBottleneckLocalProjectionSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :=
  Core.ExactHandoff
    (semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous))

noncomputable def semanticBottleneckLocalProjectionSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckLocalProjectionSource ctx overload homogeneous :=
  Core.ExactHandoff.refl
    (semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous))

structure SemanticBottleneckLocalProjection
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    Type _ where
  projection : Semantic.LocalProjection.Projection
    (geometricActivationStage ctx)
    source.output.result
  projectionExact : projection = Semantic.LocalProjection.project
    (geometricActivationStage ctx) source.output.result

noncomputable def semanticBottleneckLocalProjection
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    SemanticBottleneckLocalProjection ctx overload homogeneous source where
  projection := Semantic.LocalProjection.project
    (geometricActivationStage ctx) source.output.result
  projectionExact := rfl

theorem semanticBottleneckLocalProjectionSource_node181_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    source.output = semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous) :=
  source.outputExact

theorem semanticBottleneckLocalProjection_projection_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    (semanticBottleneckLocalProjection ctx overload homogeneous source).projection =
      Semantic.LocalProjection.project (geometricActivationStage ctx)
        source.output.result :=
  (semanticBottleneckLocalProjection ctx overload homogeneous source).projectionExact

theorem semanticBottleneckLocalProjection_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    Nonempty (Semantic.LocalProjection.Projection
      (geometricActivationStage ctx) source.output.result) :=
  Semantic.LocalProjection.project_total _ _

theorem semanticBottleneckLocalProjection_visibleChecks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Semantic.LocalProjection.visibleChecks (ctx := ctx) ≤
      ctx.G.object.input.vertices.card :=
  Semantic.LocalProjection.visibleChecks_linear

/-- The one mathematical obligation contributed by node [184]. -/
def SemanticBottleneckLocalProjectionObligation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_residual : VerifiedSemanticBottleneckClassificationPrefix ctx) : Prop :=
  ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckLocalProjection ctx overload homogeneous
        (semanticBottleneckLocalProjectionSource ctx overload homogeneous))

/-- Verified prefix through node [184]'s exact literal local projection. -/
abbrev VerifiedSemanticBottleneckLocalProjectionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State
    (VerifiedSemanticBottleneckClassificationPrefix ctx)
    [SemanticBottleneckLocalProjectionObligation ctx,
      SemanticBottleneckSwitchNormalizationObligation ctx,
      SemanticBottleneckLocalConsumerObligation ctx]

noncomputable def semanticBottleneckLocalProjectionPrefixNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SemanticBottleneckSwitchNormalizationObligation ctx,
        SemanticBottleneckLocalConsumerObligation ctx])
      (SemanticBottleneckLocalProjectionObligation ctx) where
  prove := fun _state overload homogeneous =>
    ⟨semanticBottleneckLocalProjection ctx overload homogeneous
      (semanticBottleneckLocalProjectionSource ctx overload homogeneous)⟩

noncomputable def verifiedSemanticBottleneckLocalProjectionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckSwitchNormalizationPrefix ctx) :
    VerifiedSemanticBottleneckLocalProjectionPrefix ctx :=
  (semanticBottleneckLocalProjectionPrefixNode ctx).run previous

theorem exists_verifiedSemanticBottleneckLocalProjectionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckLocalProjectionPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSemanticBottleneckSwitchNormalizationPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckLocalProjectionPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
