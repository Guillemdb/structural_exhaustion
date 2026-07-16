import Erdos64EG.CT10GeometricBottleneckClassification
import StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace Classifier
export Graph.SurplusPatternSemanticBottleneck
  (Residual classify classify_source_exact classify_total ct10Run ct10Run_terminal
    ct10Run_trace ct10Run_verified ct10Run_trace_valid ct10RunTotal
    ct10VerifiedStage classified_tag_in_ct10_table
    classificationWork classificationWork_eq classificationWork_le_vertices)
end Classifier
end Semantic

noncomputable abbrev canonicalGeometricPredecessor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :=
  coarseBottleneckClassification ctx overload homogeneous

/-! Node [177] performs only the exact retained attachment-map comparison and
the CT10 five-class residual audit.  Its aligned leaves intentionally remain
open semantic consumers. -/

structure SemanticBottleneckClassification
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  residual : Semantic.Classifier.Residual
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
  residualExact : residual = Semantic.Classifier.classify
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
  ct10 : (Graph.SurplusPatternSemanticBottleneck.ct10Profile
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).VerifiedStage
      ctx.toBranchContext
  residualAccepted :
    (Graph.SurplusPatternSemanticBottleneck.ct10Profile
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).Accepts
        residual.tag

noncomputable def semanticBottleneckClassification
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckClassification ctx overload homogeneous where
  residual := Semantic.Classifier.classify
    (geometricActivationStage ctx)
    (canonicalGeometricPredecessor ctx overload homogeneous).collision
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger
  residualExact := rfl
  ct10 := Semantic.Classifier.ct10VerifiedStage _ _ _
  residualAccepted := rfl

theorem semanticBottleneck_residual_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (semanticBottleneckClassification ctx overload homogeneous).residual =
      Semantic.Classifier.classify (geometricActivationStage ctx)
        (canonicalGeometricPredecessor ctx overload homogeneous).collision
        (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger :=
  (semanticBottleneckClassification ctx overload homogeneous).residualExact

theorem semanticBottleneck_residual_accepted
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (Graph.SurplusPatternSemanticBottleneck.ct10Profile
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).Accepts
        (semanticBottleneckClassification ctx overload homogeneous).residual.tag :=
  (semanticBottleneckClassification ctx overload homogeneous).residualAccepted

theorem semanticBottleneck_ct10_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (Graph.SurplusPatternSemanticBottleneck.ct10Profile
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).VerifiedStage
        ctx.toBranchContext :=
  (semanticBottleneckClassification ctx overload homogeneous).ct10

theorem semanticBottleneck_five_way_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    ∃ tag, Graph.SurplusPatternSemanticBottleneck.Evidence
      (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger tag :=
  Semantic.Classifier.classify_total _ _ _

/-- Exact predecessor persistence: node [177] receives the actual canonical
node-[144] trigger, including its identical germ residual and attachment maps. -/
theorem semanticBottleneck_source_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (semanticBottleneckClassification ctx overload homogeneous).residual.source =
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger :=
  Semantic.Classifier.classify_source_exact _ _ _

theorem semanticBottleneck_germ_source_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger.source =
      (canonicalGeometricPredecessor ctx overload homogeneous).germResidual := rfl

theorem semanticBottleneck_ct10_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (Semantic.Classifier.ct10Run (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).terminal =
        .exhaustive :=
  Semantic.Classifier.ct10Run_terminal _ _ _

theorem semanticBottleneck_ct10_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (Semantic.Classifier.ct10Run (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).trace =
        [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  Semantic.Classifier.ct10Run_trace _ _ _

theorem semanticBottleneck_ct10_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    (Semantic.Classifier.ct10Run (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger).outcome.Valid :=
  Semantic.Classifier.ct10Run_verified _ _ _

theorem semanticBottleneckClassificationWork_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Semantic.Classifier.classificationWork (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger =
        234 * Graph.InducedPathWindowLedger.packingNumber
          ctx.G.object + 7 := by
  apply Semantic.Classifier.classificationWork_eq

theorem semanticBottleneckClassificationWork_le_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Semantic.Classifier.classificationWork (geometricActivationStage ctx)
      (canonicalGeometricPredecessor ctx overload homogeneous).collision
      (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger ≤
        234 * ctx.G.object.input.vertices.card + 7 :=
  Semantic.Classifier.classificationWork_le_vertices _ _ _

/-- Verified prefix through node [177].  This closes the finite classifier,
not any of the four downstream aligned semantic consumers. -/
structure VerifiedSemanticBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedGeometricBottleneckClassificationPrefix ctx
  classification : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckClassification ctx overload homogeneous)

noncomputable def verifiedSemanticBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :
    VerifiedSemanticBottleneckClassificationPrefix ctx where
  previous := previous
  classification := fun overload homogeneous =>
    ⟨semanticBottleneckClassification ctx overload homogeneous⟩

theorem exists_verifiedSemanticBottleneckClassificationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSemanticBottleneckClassificationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedGeometricBottleneckClassificationPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedSemanticBottleneckClassificationPrefix ctx previous⟩

end Erdos64EG.Internal
