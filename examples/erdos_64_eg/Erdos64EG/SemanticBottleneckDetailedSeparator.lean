import Erdos64EG.SemanticBottleneckLocalConsumer
import StructuralExhaustion.Graph.SurplusPatternDetailedSeparator

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace DetailedSeparator
export Graph.SurplusPatternDetailedSeparator
  (Result classify classify_total checks checks_eq_ten RootHighData
    AfterEdgeHighData rootDivergentPairOutcome afterEdgeDivergentPairOutcome
    rootDivergentPairOutcome_total afterEdgeDivergentPairOutcome_total
    rootDivergentPairSurvivor afterEdgeDivergentPairSurvivor)
end DetailedSeparator
end Semantic

/-!
# Incidence-preserving support after node [178]

This is a thin execution of the graph-owned detailed separator classifier on
the exact node-[178] output.  It preserves root/after-edge incidences on high
leaves and exposes the locally complete four-cycle/compatible/open--open split.
It is support for repairing node [144], not a completed node or Type-B handoff.
-/

structure SemanticBottleneckDetailedSeparator
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  previous : SemanticBottleneckLocalConsumer ctx overload homogeneous
  result : Semantic.DetailedSeparator.Result
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    previous.previous.residual previous.frontier
  resultExact : result = Semantic.DetailedSeparator.classify
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
    previous.previous.residual previous.frontier

noncomputable def semanticBottleneckDetailedSeparator
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckDetailedSeparator ctx overload homogeneous := by
  let previous := semanticBottleneckLocalConsumer ctx overload homogeneous
  exact {
    previous := previous
    result := Semantic.DetailedSeparator.classify
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
      previous.previous.residual previous.frontier
    resultExact := rfl
  }

theorem semanticBottleneckDetailedSeparator_result_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (semanticBottleneckDetailedSeparator ctx overload homogeneous).result =
      Semantic.DetailedSeparator.classify (geometricActivationStage ctx)
        (canonicalGeometricPredecessor ctx overload homogeneous).collision
        (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
        (semanticBottleneckDetailedSeparator ctx overload homogeneous
          ).previous.previous.residual
        (semanticBottleneckDetailedSeparator ctx overload homogeneous
          ).previous.frontier :=
  (semanticBottleneckDetailedSeparator ctx overload homogeneous).resultExact

theorem semanticBottleneckDetailedSeparator_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Nonempty (Semantic.DetailedSeparator.Result
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
      (semanticBottleneckLocalConsumer ctx overload homogeneous).previous.residual
      (semanticBottleneckLocalConsumer ctx overload homogeneous).frontier) :=
  Semantic.DetailedSeparator.classify_total _ _ _ _ _

theorem semanticBottleneckDetailedSeparator_checks_eq_ten :
    Semantic.DetailedSeparator.checks = 10 :=
  Semantic.DetailedSeparator.checks_eq_ten

end Erdos64EG.Internal
