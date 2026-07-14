import Erdos64EG.CT1HighCenterStructure

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT10: selected surplus-port classification

This application layer supplies no search logic.  The graph-owned profile
canonically selects the `degree - 3` surplus ports at every centre, derives
their two shoulder vertices from deletion criticality, and classifies each
port as open or triangular.  CT10 scans that explicit slot list against the
two-element type universe.
-/

abbrev surplusPortClassificationCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.classificationCapability
    (fixedPackedInput ctx) ctx.G.object
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev surplusPortClassificationInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.classificationInput
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def runSurplusPortClassificationCT10
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.classificationRun
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def surplusPortClassificationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.VerifiedClassificationStage
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) :=
  Graph.SurplusPortActivity.verifiedClassificationStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem surplusPortClassification_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (∃ cls : Graph.SurplusPortActivity.PortType,
        CT10.row (surplusPortClassificationCapability ctx)
          (surplusPortClassificationInput ctx) cls = []) ∨
      (∀ cls : Graph.SurplusPortActivity.PortType,
        ∃ slot : Graph.SurplusPortActivity.ExcessPortSlot ctx.G.object,
          slot ∈ CT10.row (surplusPortClassificationCapability ctx)
            (surplusPortClassificationInput ctx) cls) :=
  (surplusPortClassificationStage ctx).stateSpace

theorem runSurplusPortClassificationCT10_checks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.classificationChecks ctx.G.object ≤
      2 * ctx.G.object.input.vertices.card ^ 2 + 2 :=
  (surplusPortClassificationStage ctx).polynomial

structure VerifiedSurplusPortClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedHighCenterStructurePrefix ctx
  stage : Graph.SurplusPortActivity.VerifiedClassificationStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def verifiedSurplusPortClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :
    VerifiedSurplusPortClassificationPrefix ctx where
  previous := previous
  stage := surplusPortClassificationStage ctx

theorem exists_verifiedSurplusPortClassificationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSurplusPortClassificationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedHighCenterStructurePrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedSurplusPortClassificationPrefix ctx previous⟩

end Erdos64EG.Internal
