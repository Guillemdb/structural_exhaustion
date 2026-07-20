import Erdos64EG.Future.CT1HighCenterStructure

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

abbrev surplusPortClassificationEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (surplusPortClassificationCapability ctx).executableInterface

/-- The only problem-specific data for the real CT1→CT10 manuscript edge.
The adapter reads no hidden state and exposes the graph-owned local schedule. -/
abbrev surplusPortClassificationAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :
    Routes.Accumulated.Adapter (HighCenterStructureLedger ctx previous)
      (surplusPortClassificationEntry ctx) :=
  Graph.SurplusPortActivity.classificationAdapter
    (Source := HighCenterStructureLedger ctx previous)
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- Sole framework-owned CT1→CT10 transition for this application stage. -/
abbrev surplusPortClassificationTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :=
  Routes.Accumulated.transition (sourceTactic := .ct1)
    (surplusPortClassificationEntry ctx)
    (surplusPortClassificationAdapter ctx previous)

abbrev SurplusPortClassificationSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :=
  Core.Routing.ResidualStage .ct1 (HighCenterStructureLedger ctx previous)

abbrev SurplusPortClassificationEnabledStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :=
  Routes.Accumulated.OutputLedger
    (surplusPortClassificationEntry ctx)
    (surplusPortClassificationAdapter ctx previous)
    (highCenterStructureLedgerStage ctx previous)

/-- The application prefix is only the dependent framework stage; its exact
source stage is the first component and the enabled target execution is the
second.  No application-owned predecessor handoff remains. -/
abbrev VerifiedSurplusPortClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedHighCenterStructurePrefix ctx =>
    Core.Routing.ResidualStage .ct10
      (SurplusPortClassificationEnabledStage ctx previous)

/-- Execute CT10 from the literal complete CT1-labelled application prefix. -/
def surplusPortClassificationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :
    Core.Routing.ResidualStage .ct10
      (SurplusPortClassificationEnabledStage ctx previous) :=
  Routes.Accumulated.advanceCurrent (surplusPortClassificationEntry ctx)
    (surplusPortClassificationAdapter ctx previous)
    (highCenterStructureLedgerStage ctx previous)

/-- The literal target execution returned by the transition, never a second
call to the CT10 runner. -/
def runSurplusPortClassificationCT10
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPortClassificationPrefix ctx) :=
  verified.2.output.targetResult

/-- Canonical CT10 ledger for the next manuscript edge. -/
def surplusPortClassificationLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPortClassificationPrefix ctx) :=
  verified.2

theorem surplusPortClassificationTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :
    (surplusPortClassificationTransition ctx previous).profileId =
      "CT1.residual.accumulatedLedger->CT10" :=
  Routes.Accumulated.transition_profile_id
    (sourceTactic := .ct1)
    (surplusPortClassificationEntry ctx)
    (surplusPortClassificationAdapter ctx previous)

theorem runSurplusPortClassificationCT10_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPortClassificationPrefix ctx) :
    (runSurplusPortClassificationCT10 ctx verified).outcome.Valid :=
  (runSurplusPortClassificationCT10 ctx verified).verified

theorem runSurplusPortClassificationCT10_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPortClassificationPrefix ctx) :
    CT10.Graph.ValidTrace (surplusPortClassificationCapability ctx)
      (surplusPortClassificationInput ctx)
      (runSurplusPortClassificationCT10 ctx verified).trace :=
  (runSurplusPortClassificationCT10 ctx verified).traceValid

theorem surplusPortClassification_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPortClassificationPrefix ctx) :
    (∃ cls : Graph.SurplusPortActivity.PortType,
        CT10.row (surplusPortClassificationCapability ctx)
          (surplusPortClassificationInput ctx) cls = []) ∨
      (∀ cls : Graph.SurplusPortActivity.PortType,
        ∃ slot : Graph.SurplusPortActivity.ExcessPortSlot ctx.G.object,
          slot ∈ CT10.row (surplusPortClassificationCapability ctx)
            (surplusPortClassificationInput ctx) cls) :=
  Graph.SurplusPortActivity.classificationResult_stateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (runSurplusPortClassificationCT10 ctx verified)

theorem runSurplusPortClassificationCT10_checks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.classificationChecks ctx.G.object ≤
      2 * ctx.G.object.input.vertices.card ^ 2 + 2 :=
  Graph.SurplusPortActivity.classificationChecks_quadratic ctx.G.object

def verifiedSurplusPortClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterStructurePrefix ctx) :
    VerifiedSurplusPortClassificationPrefix ctx :=
  ⟨previous, surplusPortClassificationStage ctx previous⟩

theorem exists_verifiedSurplusPortClassificationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSurplusPortClassificationPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedHighCenterStructurePrefix object baseline avoids
  exact ⟨ctx, verifiedSurplusPortClassificationPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
