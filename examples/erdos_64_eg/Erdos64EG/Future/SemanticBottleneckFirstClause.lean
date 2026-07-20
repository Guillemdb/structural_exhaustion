import Erdos64EG.Future.SemanticBottleneckStrongFrontier
import StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace FirstClause
export Graph.SurplusPatternFirstSemanticClause
  (Certificate Result certify run run_total visibleChecks visibleChecks_constant)
end FirstClause
end Semantic

/-!
# Node [190]: first graph-derived local separator clause

This node consumes node [187]'s exact retained payload and obligation tag.
Cubic leaves yield their three literal boundary incidences; high leaves yield
four injective declared ports and adjacent endpoints; mismatch and prefix
leaves remain exact pass-through certificates.  No strong semantic obligation
is discharged. Node [193] is the sole successor.
-/

abbrev SemanticBottleneckFirstClauseSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :=
  Core.ExactHandoff
    (semanticBottleneckStrongFrontier ctx overload homogeneous
      (semanticBottleneckStrongFrontierSource ctx overload homogeneous))

noncomputable def semanticBottleneckFirstClauseSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckFirstClauseSource ctx overload homogeneous :=
  Core.ExactHandoff.refl
    (semanticBottleneckStrongFrontier ctx overload homogeneous
      (semanticBottleneckStrongFrontierSource ctx overload homogeneous))

structure SemanticBottleneckFirstClause
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    Type _ where
  result : Semantic.FirstClause.Result
    (geometricActivationStage ctx) source.output.pending
  resultExact : result = Semantic.FirstClause.run
    (geometricActivationStage ctx) source.output.pending

noncomputable def semanticBottleneckFirstClause
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    SemanticBottleneckFirstClause ctx overload homogeneous source where
  result := Semantic.FirstClause.run
    (geometricActivationStage ctx) source.output.pending
  resultExact := rfl

theorem semanticBottleneckFirstClauseSource_node187_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    source.output = semanticBottleneckStrongFrontier ctx overload homogeneous
      (semanticBottleneckStrongFrontierSource ctx overload homogeneous) :=
  source.outputExact

theorem semanticBottleneckFirstClause_result_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    (semanticBottleneckFirstClause ctx overload homogeneous source).result =
      Semantic.FirstClause.run (geometricActivationStage ctx)
        source.output.pending :=
  (semanticBottleneckFirstClause ctx overload homogeneous source).resultExact

theorem semanticBottleneckFirstClause_obligation_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    source.output.pending.obligation =
      Graph.SurplusPatternStrongSemanticFrontier.required
        (geometricActivationStage ctx) source.output.pending.retained :=
  (semanticBottleneckFirstClause ctx overload homogeneous source).result.obligationExact

theorem semanticBottleneckFirstClause_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckFirstClauseSource ctx overload homogeneous) :
    Nonempty (Semantic.FirstClause.Result
      (geometricActivationStage ctx) source.output.pending) :=
  Semantic.FirstClause.run_total _ _

theorem semanticBottleneckFirstClause_visibleChecks_constant :
    Semantic.FirstClause.visibleChecks ≤ 4 :=
  Semantic.FirstClause.visibleChecks_constant

def SemanticBottleneckFirstClauseObligation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_residual : VerifiedSemanticBottleneckClassificationPrefix ctx) : Prop :=
  ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckFirstClause ctx overload homogeneous
        (semanticBottleneckFirstClauseSource ctx overload homogeneous))

abbrev VerifiedSemanticBottleneckFirstClausePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.ResidualRefinement.State
    (VerifiedSemanticBottleneckClassificationPrefix ctx)
    [SemanticBottleneckFirstClauseObligation ctx,
      SemanticBottleneckStrongFrontierObligation ctx,
      SemanticBottleneckLocalProjectionObligation ctx,
      SemanticBottleneckSwitchNormalizationObligation ctx,
      SemanticBottleneckLocalConsumerObligation ctx]

noncomputable def semanticBottleneckFirstClausePrefixNode
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.ResidualRefinement.State.Node
      (facts := [SemanticBottleneckStrongFrontierObligation ctx,
        SemanticBottleneckLocalProjectionObligation ctx,
        SemanticBottleneckSwitchNormalizationObligation ctx,
        SemanticBottleneckLocalConsumerObligation ctx])
      (SemanticBottleneckFirstClauseObligation ctx) where
  prove := fun _state overload homogeneous =>
    ⟨semanticBottleneckFirstClause ctx overload homogeneous
      (semanticBottleneckFirstClauseSource ctx overload homogeneous)⟩

noncomputable def verifiedSemanticBottleneckFirstClausePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckStrongFrontierPrefix ctx) :
    VerifiedSemanticBottleneckFirstClausePrefix ctx :=
  (semanticBottleneckFirstClausePrefixNode ctx).run previous

theorem exists_verifiedSemanticBottleneckFirstClausePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckFirstClausePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSemanticBottleneckStrongFrontierPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckFirstClausePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
