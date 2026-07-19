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

abbrev openPortPairEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (openPortPairCapability ctx).executableInterface

abbrev OpenPortPairSourceLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :=
  SurplusPortClassificationEnabledStage ctx previous.1

/-- The sole graph-specific adapter for the real CT10→CT9 manuscript edge. -/
abbrev openPortPairAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :
    Routes.Accumulated.Adapter (OpenPortPairSourceLedger ctx previous)
      (openPortPairEntry ctx) :=
  Graph.SurplusPortActivity.openPairAdapter
    (Source := OpenPortPairSourceLedger ctx previous)
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- Sole framework-owned CT10→CT9 transition at this paper edge. -/
abbrev openPortPairTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  fun previous : VerifiedSurplusPortClassificationPrefix ctx =>
    Routes.Accumulated.transition (sourceTactic := .ct10)
      (openPortPairEntry ctx) (openPortPairAdapter ctx previous)

abbrev OpenPortPairEnabledStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :=
  Routes.Accumulated.OutputLedger (openPortPairEntry ctx)
    (openPortPairAdapter ctx previous) previous.2

/-- Complete CT9 application prefix, represented only by the prior dependent
framework stage and the newly enabled stage. -/
abbrev VerifiedOpenPortPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedSurplusPortClassificationPrefix ctx =>
    Core.Routing.ResidualStage .ct9 (OpenPortPairEnabledStage ctx previous)

/-- Execute CT9 directly from the prior CT10 stage's canonical ledger. -/
def openPortPairStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :
    Core.Routing.ResidualStage .ct9 (OpenPortPairEnabledStage ctx previous) :=
  Routes.Accumulated.advanceCurrent (openPortPairEntry ctx)
    (openPortPairAdapter ctx previous) previous.2

/-- Literal CT9 target result from the accumulated transition. -/
def runOpenPortPairCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedOpenPortPairPrefix ctx) :=
  verified.2.output.targetResult

/-- Canonical CT9 ledger passed to the next paper transition. -/
def openPortPairLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedOpenPortPairPrefix ctx) :=
  verified.2

def openPortPairDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedOpenPortPairPrefix ctx) :=
  Graph.SurplusPortActivity.openPairDecisionOfResult
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (runOpenPortPairCT9 ctx verified)

theorem openPortPairTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :
    (openPortPairTransition ctx previous).profileId =
      "CT10.residual.accumulatedLedger->CT9" :=
  Routes.Accumulated.transition_profile_id
    (sourceTactic := .ct10)
    (openPortPairEntry ctx) (openPortPairAdapter ctx previous)

theorem runOpenPortPairCT9_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedOpenPortPairPrefix ctx) :
    (runOpenPortPairCT9 ctx verified).outcome.Valid :=
  (runOpenPortPairCT9 ctx verified).verified

theorem runOpenPortPairCT9_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedOpenPortPairPrefix ctx) :
    CT9.Graph.ValidTrace (openPortPairCapability ctx) (openPortPairInput ctx)
      (runOpenPortPairCT9 ctx verified).trace :=
  (runOpenPortPairCT9 ctx verified).traceValid

theorem runOpenPortPairCT9_checks_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.openPairChecks ctx.G.object
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) ≤
      ctx.G.object.input.vertices.card ^ 3 +
        ctx.G.object.input.vertices.card :=
  Graph.SurplusPortActivity.openPairChecks_cubic ctx.G.object
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def verifiedOpenPortPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortClassificationPrefix ctx) :
    VerifiedOpenPortPairPrefix ctx :=
  ⟨previous, openPortPairStage ctx previous⟩

theorem exists_verifiedOpenPortPairPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedOpenPortPairPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSurplusPortClassificationPrefix object baseline avoids
  exact ⟨ctx, verifiedOpenPortPairPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
