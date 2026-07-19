import Erdos64EG.CT10SemanticBottleneckClassification
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Graph.SurplusPatternSemanticConsumer

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace Consumer
export Graph.SurplusPatternSemanticConsumer
  (Frontier classify classify_total checks checks_le_linear)
end Consumer
end Semantic

/-! Node [178] is the first honest consumer of node [177]'s five residual
leaves.  It performs only the separator-incidence and cubic/high split that is
already determined by the stored rooted paths.  No sparse-exit, CT3, Type-B,
fixed-cap, or near-cubic conclusion is attached here. -/

structure SemanticBottleneckLocalConsumer
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u
    extends Core.ExactHandoff
      (semanticBottleneckClassification ctx overload homogeneous) where
  frontier : Semantic.Consumer.Frontier
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    previous.residual
  frontierExact : frontier = Semantic.Consumer.classify
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    previous.residual

noncomputable def semanticBottleneckLocalConsumer
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckLocalConsumer ctx overload homogeneous := by
  let previous := semanticBottleneckClassification ctx overload homogeneous
  exact {
    toExactHandoff := Core.ExactHandoff.refl previous
    frontier := Semantic.Consumer.classify
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
      previous.residual
    frontierExact := rfl
  }

theorem semanticBottleneckLocalConsumer_previous_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (semanticBottleneckLocalConsumer ctx overload homogeneous).previous =
      semanticBottleneckClassification ctx overload homogeneous :=
  (semanticBottleneckLocalConsumer ctx overload homogeneous).previousExact

theorem semanticBottleneckLocalConsumer_frontier_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (semanticBottleneckLocalConsumer ctx overload homogeneous).frontier =
      Semantic.Consumer.classify (geometricActivationStage ctx)
        (canonicalGeometricPredecessor ctx overload homogeneous).collision
        (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
        (semanticBottleneckLocalConsumer ctx overload homogeneous).previous.residual :=
  (semanticBottleneckLocalConsumer ctx overload homogeneous).frontierExact

theorem semanticBottleneckLocalConsumer_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Nonempty (Semantic.Consumer.Frontier
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
      (semanticBottleneckClassification ctx overload homogeneous).residual) :=
  Semantic.Consumer.classify_total _ _ _ _

theorem semanticBottleneckLocalConsumer_checks_le_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Semantic.Consumer.checks
      (ctx := ctx) ≤ ctx.G.object.input.vertices.card + 1 :=
  Semantic.Consumer.checks_le_linear

/-- The one mathematical obligation contributed by node [178]. -/
def SemanticBottleneckLocalConsumerObligation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedSemanticBottleneckClassificationPrefix ctx) : Prop :=
  ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckLocalConsumer ctx overload homogeneous)

/-- Verified prefix through the corrected finite meaning of node [178].  The
framework state retains the literal incoming prefix and its complete proof
ledger; this node contributes only its local consumer obligation. -/
abbrev VerifiedSemanticBottleneckLocalConsumerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State
    (VerifiedSemanticBottleneckClassificationPrefix ctx)
    [SemanticBottleneckLocalConsumerObligation ctx]

noncomputable def semanticBottleneckLocalConsumerPrefixNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node (facts := [])
      (SemanticBottleneckLocalConsumerObligation ctx) where
  prove := fun _state overload homogeneous =>
    ⟨semanticBottleneckLocalConsumer ctx overload homogeneous⟩

noncomputable def verifiedSemanticBottleneckLocalConsumerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckClassificationPrefix ctx) :
    VerifiedSemanticBottleneckLocalConsumerPrefix ctx :=
  (semanticBottleneckLocalConsumerPrefixNode ctx).run
    (Core.ResidualRefinement.State.initial previous)

theorem exists_verifiedSemanticBottleneckLocalConsumerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckLocalConsumerPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSemanticBottleneckClassificationPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckLocalConsumerPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
