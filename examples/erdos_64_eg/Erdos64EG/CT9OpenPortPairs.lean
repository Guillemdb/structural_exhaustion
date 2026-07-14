import Erdos64EG.CT10SurplusPortClassification

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: selected open ports grouped by centre

The reusable graph profile filters the already canonical surplus-slot family
to open ports and applies capacity-one CT9 fibres labelled by the actual
centre.  No pairs are enumerated: overload extracts one pair from the first
overloaded centre fibre, while the dual terminal certifies at most one open
selected port at every centre.
-/

abbrev openPortPairCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.openPairCapability
    (fixedPackedInput ctx) ctx.G.object
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev openPortPairInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.openPairInput
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def runOpenPortPairCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.openPairResult
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def openPortPairDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.openPairDecision
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def openPortPairStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.VerifiedOpenPairStage
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) :=
  Graph.SurplusPortActivity.verifiedOpenPairStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem runOpenPortPairCT9_checks_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.openPairChecks ctx.G.object
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) ≤
      ctx.G.object.input.vertices.card ^ 3 +
        ctx.G.object.input.vertices.card :=
  (openPortPairStage ctx).polynomial

structure VerifiedOpenPortPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSurplusPortClassificationPrefix ctx
  stage : Graph.SurplusPortActivity.VerifiedOpenPairStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def verifiedOpenPortPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :
    VerifiedOpenPortPairPrefix ctx where
  previous := previous
  stage := openPortPairStage ctx

theorem exists_verifiedOpenPortPairPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedOpenPortPairPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSurplusPortClassificationPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedOpenPortPairPrefix ctx previous⟩

end Erdos64EG.Internal
