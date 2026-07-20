import Erdos64EG.Future.CT10GeometricBottleneckClassification
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

/-- Exact dependent index of the manuscript's already selected overload and
homogeneous-pattern branches.  It is used pointwise and is never enumerated. -/
abbrev SemanticBottleneckClassificationIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type u :=
  Sigma fun overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx) =>
    Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)

/-- Framework pointwise CT9→CT10 profile.  Every local index executes its own
public exhaustive-classification capability while the complete geometric
ledger is retained exactly once. -/
noncomputable def semanticBottleneckPointwiseProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :
    Routes.Accumulated.PointwiseAdapter
      .ct9 .ct10
      (SemanticBottleneckClassificationIndex ctx)
      (GeometricBottleneckClassificationLedger ctx previous.1) where
  Source := fun _index =>
    GeometricBottleneckClassificationLedger ctx previous.1
  target := fun index =>
    let predecessor := canonicalGeometricPredecessor ctx index.1 index.2
    let profile := Graph.SurplusPatternSemanticBottleneck.ct10Profile
      (geometricActivationStage ctx) predecessor.collision
      predecessor.semanticTrigger
    (profile.capability PackedProblem.{u}).executableInterface
  adapter := fun index =>
    let predecessor := canonicalGeometricPredecessor ctx index.1 index.2
    let profile := Graph.SurplusPatternSemanticBottleneck.ct10Profile
      (geometricActivationStage ctx) predecessor.collision
      predecessor.semanticTrigger
    {
      targetContext := fun _source => ctx.toBranchContext
      trigger := fun _source =>
        ⟨(profile.input ctx.toBranchContext).data⟩
    }
  current := fun _index => id

noncomputable def semanticBottleneckTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :=
  Routes.Accumulated.advancePointwise
    (semanticBottleneckPointwiseProfile ctx previous)
    (geometricBottleneckClassificationLedgerStage ctx previous)

abbrev SemanticBottleneckTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :=
  Routes.Accumulated.PointwiseOutputLedger
    (semanticBottleneckPointwiseProfile ctx previous)
    (geometricBottleneckClassificationLedgerStage ctx previous)

/-- Node `[177]` obligations attached to the exact pointwise CT10 execution. -/
structure SemanticBottleneckClassificationFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedGeometricBottleneckClassificationPrefix ctx}
    (_stage : SemanticBottleneckTransitionLedger ctx previous) : Prop where
  classification : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (SemanticBottleneckClassification ctx overload homogeneous)

abbrev SemanticBottleneckClassificationLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :=
  Core.Routing.LedgerExtension
    (SemanticBottleneckTransitionLedger ctx previous)
    (SemanticBottleneckClassificationFacts ctx)

/-- Verified prefix through node `[177]`; no aligned semantic consumer is
claimed here. -/
abbrev VerifiedSemanticBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedGeometricBottleneckClassificationPrefix ctx =>
    Core.Routing.ResidualStage .ct10
      (SemanticBottleneckClassificationLedger ctx previous)

noncomputable def verifiedSemanticBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedGeometricBottleneckClassificationPrefix ctx) :
    VerifiedSemanticBottleneckClassificationPrefix ctx :=
  let stage := semanticBottleneckTransitionStage ctx previous
  ⟨previous, stage.extend {
    classification := fun overload homogeneous =>
      ⟨semanticBottleneckClassification ctx overload homogeneous⟩
  }⟩

/-- Canonical complete CT10 continuation stage after node `[177]`. -/
noncomputable def semanticBottleneckClassificationLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSemanticBottleneckClassificationPrefix ctx) :=
  verified.2

theorem exists_verifiedSemanticBottleneckClassificationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSemanticBottleneckClassificationPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedGeometricBottleneckClassificationPrefix object baseline avoids
  exact ⟨ctx,
    verifiedSemanticBottleneckClassificationPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
