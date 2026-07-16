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

structure SemanticBottleneckLocalProjectionSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  node181 : SemanticBottleneckSwitchNormalization ctx overload homogeneous
    (semanticBottleneckNormalizationSource ctx overload homogeneous)
  node181Exact : node181 =
    semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous)

noncomputable def semanticBottleneckLocalProjectionSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckLocalProjectionSource ctx overload homogeneous :=
  ⟨semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous), rfl⟩

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
    source.node181.result
  projectionExact : projection = Semantic.LocalProjection.project
    (geometricActivationStage ctx) source.node181.result

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
    (geometricActivationStage ctx) source.node181.result
  projectionExact := rfl

theorem semanticBottleneckLocalProjectionSource_node181_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckLocalProjectionSource ctx overload homogeneous) :
    source.node181 = semanticBottleneckSwitchNormalization ctx overload homogeneous
      (semanticBottleneckNormalizationSource ctx overload homogeneous) :=
  source.node181Exact

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
        source.node181.result :=
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
      (geometricActivationStage ctx) source.node181.result) :=
  Semantic.LocalProjection.project_total _ _

theorem semanticBottleneckLocalProjection_visibleChecks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Semantic.LocalProjection.visibleChecks (ctx := ctx) ≤
      ctx.G.object.input.vertices.card :=
  Semantic.LocalProjection.visibleChecks_linear

/-- Verified prefix through node [184]'s exact literal local projection. -/
structure VerifiedSemanticBottleneckLocalProjectionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSemanticBottleneckSwitchNormalizationPrefix ctx
  projection : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckLocalProjection ctx overload homogeneous
        (semanticBottleneckLocalProjectionSource ctx overload homogeneous))

noncomputable def verifiedSemanticBottleneckLocalProjectionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckSwitchNormalizationPrefix ctx) :
    VerifiedSemanticBottleneckLocalProjectionPrefix ctx where
  previous := previous
  projection := fun overload homogeneous =>
    ⟨semanticBottleneckLocalProjection ctx overload homogeneous
      (semanticBottleneckLocalProjectionSource ctx overload homogeneous)⟩

theorem exists_verifiedSemanticBottleneckLocalProjectionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSemanticBottleneckLocalProjectionPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSemanticBottleneckSwitchNormalizationPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedSemanticBottleneckLocalProjectionPrefix ctx previous⟩

end Erdos64EG.Internal
