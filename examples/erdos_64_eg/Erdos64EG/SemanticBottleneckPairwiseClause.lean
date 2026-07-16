import Erdos64EG.SemanticBottleneckFirstClause
import StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace PairwiseClause
export Graph.SurplusPatternPairwiseSemanticClause
  (Clause Result derive run run_total visibleChecks visibleChecks_eq_zero)
end PairwiseClause
end Semantic

/-!
# Node [193]: pairwise local separator clauses

The exact node-[190] certificate yields only pairwise endpoint inequalities
and centre-to-endpoint inequalities. The pending node-[187] obligation remains
unchanged. This is the terminal residual interface at the manuscript boundary.
-/

structure SemanticBottleneckPairwiseClauseSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  node190 : SemanticBottleneckFirstClause ctx overload homogeneous
    (semanticBottleneckFirstClauseSource ctx overload homogeneous)
  node190Exact : node190 = semanticBottleneckFirstClause ctx overload homogeneous
    (semanticBottleneckFirstClauseSource ctx overload homogeneous)

noncomputable def semanticBottleneckPairwiseClauseSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckPairwiseClauseSource ctx overload homogeneous :=
  ⟨semanticBottleneckFirstClause ctx overload homogeneous
      (semanticBottleneckFirstClauseSource ctx overload homogeneous), rfl⟩

structure SemanticBottleneckPairwiseClause
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    Type _ where
  result : Semantic.PairwiseClause.Result
    (geometricActivationStage ctx) source.node190.result
  resultExact : result = Semantic.PairwiseClause.run
    (geometricActivationStage ctx) source.node190.result

noncomputable def semanticBottleneckPairwiseClause
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    SemanticBottleneckPairwiseClause ctx overload homogeneous source where
  result := Semantic.PairwiseClause.run
    (geometricActivationStage ctx) source.node190.result
  resultExact := rfl

theorem semanticBottleneckPairwiseClauseSource_node190_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    source.node190 = semanticBottleneckFirstClause ctx overload homogeneous
      (semanticBottleneckFirstClauseSource ctx overload homogeneous) :=
  source.node190Exact

theorem semanticBottleneckPairwiseClause_result_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    (semanticBottleneckPairwiseClause ctx overload homogeneous source).result =
      Semantic.PairwiseClause.run (geometricActivationStage ctx)
        source.node190.result :=
  (semanticBottleneckPairwiseClause ctx overload homogeneous source).resultExact

theorem semanticBottleneckPairwiseClause_obligation_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    source.node190.result.obligationExact =
      (semanticBottleneckPairwiseClause ctx overload homogeneous source
        ).result.obligationExact := by
  apply proof_irrel

theorem semanticBottleneckPairwiseClause_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (source : SemanticBottleneckPairwiseClauseSource ctx overload homogeneous) :
    Nonempty (Semantic.PairwiseClause.Result
      (geometricActivationStage ctx) source.node190.result) :=
  Semantic.PairwiseClause.run_total _ _

theorem semanticBottleneckPairwiseClause_visibleChecks_eq_zero :
    Semantic.PairwiseClause.visibleChecks = 0 :=
  Semantic.PairwiseClause.visibleChecks_eq_zero

structure VerifiedSemanticBottleneckPairwiseClausePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSemanticBottleneckFirstClausePrefix ctx
  clause : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckPairwiseClause ctx overload homogeneous
        (semanticBottleneckPairwiseClauseSource ctx overload homogeneous))

noncomputable def verifiedSemanticBottleneckPairwiseClausePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSemanticBottleneckFirstClausePrefix ctx) :
    VerifiedSemanticBottleneckPairwiseClausePrefix ctx where
  previous := previous
  clause := fun overload homogeneous =>
    ⟨semanticBottleneckPairwiseClause ctx overload homogeneous
      (semanticBottleneckPairwiseClauseSource ctx overload homogeneous)⟩

theorem exists_verifiedSemanticBottleneckPairwiseClausePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object) (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSemanticBottleneckPairwiseClausePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSemanticBottleneckFirstClausePrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedSemanticBottleneckPairwiseClausePrefix ctx previous⟩

end Erdos64EG.Internal
