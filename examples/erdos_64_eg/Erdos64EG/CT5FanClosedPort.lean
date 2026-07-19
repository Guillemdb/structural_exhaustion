import Erdos64EG.CT9TriangularCrossShoulder
import StructuralExhaustion.Graph.FanClosedPort
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v w

/-!
# CT5: fan-compatible open pairs give fan-closed local data

The application supplies the actual packed-window set `W`, its exact
remainder `R = G - W`, and the Type-B assignment predicate.  The framework
derives the two fan-closure conclusions, the four distinct local carriers,
and the complete constant-work CT5 execution.
-/

/-- Erdős `P₁₃` window/remainder interpretation of the generic fan profile.
Only the assigned-incidence predicate remains an input of the later Type-B
construction. -/
noncomputable def p13FanWindowProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier)) :
    Graph.FanClosedPort.FanWindowProfile ctx.G.Vertex where
  WindowSide := fun vertex => vertex ∈ p13CoveredVertices ctx
  RemainderSide := fun vertex => vertex ∈ p13RemainderVertices ctx
  Assigned := Assigned
  windowDecidable := fun vertex => by classical infer_instance
  remainderDecidable := fun vertex => by classical infer_instance
  assignedDecidable := assignedDecidable
  remainder_not_window := by
    intro vertex remainder
    simpa [p13RemainderVertices, p13CoveredVertices,
      Graph.InducedPathPacking.remainderVertices] using remainder

abbrev FanClosedOpenPort
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.FanClosedPort.OpenPort centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev FanClosedPairStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (first second : FanClosedOpenPort ctx center centerHigh)
    (pair : Graph.FanClosedPort.CompatiblePair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) first second)
    (assigned : Graph.FanClosedPort.AssignedPair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx Assigned assignedDecidable) first second) :=
  Graph.FanClosedPort.VerifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

noncomputable def fanClosedPairStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (first second : FanClosedOpenPort ctx center centerHigh)
    (pair : Graph.FanClosedPort.CompatiblePair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) first second)
    (assigned : Graph.FanClosedPort.AssignedPair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx Assigned assignedDecidable) first second) :
    FanClosedPairStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned :=
  Graph.FanClosedPort.verifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

/-- One proof-selected local fan-closure request.  Requests are consumed
pointwise; this type is never enumerated. -/
structure FanClosedPortRequest
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  center : ctx.G.Vertex
  centerHigh : 4 ≤ ctx.G.object.degree center
  Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop
  assignedDecidable : ∀ carrier, Decidable (Assigned carrier)
  first : FanClosedOpenPort ctx center centerHigh
  second : FanClosedOpenPort ctx center centerHigh
  pair : Graph.FanClosedPort.CompatiblePair centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) first second
  assigned : Graph.FanClosedPort.AssignedPair centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable) first second

noncomputable def fanClosedPortFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.Routing.PointwiseExecutableFamily .ct5 where
  Index := FanClosedPortRequest ctx
  entry := fun request =>
    (Graph.FanClosedPort.capability (base := fixedPackedInput ctx)
      request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second).executableInterface
  context := fun _request =>
    Graph.FanClosedPort.input (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
  trigger := fun _request => ()

def fanClosedPortAdapter {Source : Sort w}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source
      (fanClosedPortFamily ctx).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

noncomputable def fanClosedPortTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (fanClosedPortFamily ctx).executableInterface
    (fanClosedPortAdapter ctx) source

abbrev FanClosedPortTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.OutputLedger
    (fanClosedPortFamily ctx).executableInterface
    (fanClosedPortAdapter ctx) source

/-- Graph semantics proved about the literal pointwise CT5 result retained by
the accumulated transition.  Downstream consumers never unfold the executor
to reconnect an independently stated theorem. -/
structure FanClosedPortFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (execution : FanClosedPortTransitionLedger ctx source) : Prop where
  stage : ∀ request : FanClosedPortRequest ctx,
    FanClosedPairStage ctx request.center request.centerHigh
      request.Assigned request.assignedDecidable request.first request.second
      request.pair request.assigned
  terminal : ∀ request : FanClosedPortRequest ctx,
    (execution.targetResult request).terminal = .charge

abbrev FanClosedPortLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Core.Routing.LedgerExtension
    (FanClosedPortTransitionLedger ctx source)
    (FanClosedPortFacts ctx)

noncomputable def fanClosedPortLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :
    Core.Routing.ResidualStage .ct5 (FanClosedPortLedger ctx source) :=
  let execution := fanClosedPortTransitionStage ctx source
  execution.ledgerStage.extend {
    stage := fun request =>
      fanClosedPairStage ctx request.center request.centerHigh
        request.Assigned request.assignedDecidable request.first request.second
        request.pair request.assigned
    terminal := by
      intro request
      change (Graph.FanClosedPort.run
        (base := fixedPackedInput ctx)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        request.centerHigh
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx))
        (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
        request.first request.second).terminal = .charge
      exact (fanClosedPairStage ctx request.center request.centerHigh
        request.Assigned request.assignedDecidable request.first request.second
        request.pair request.assigned).terminal
  }

noncomputable def runFanClosedPortCT5
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (stage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx source)) :=
  stage.output.previous.targetResult

/-- The exact charge residual at one request, extracted from the literal
pointwise target result and its attached terminal theorem. -/
noncomputable def fanClosedPortChargeResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (ledger : FanClosedPortLedger ctx source)
    (request : FanClosedPortRequest ctx) :=
  CT5.ExecutionResult.chargeResidual
    (Graph.FanClosedPort.spec (base := fixedPackedInput ctx)
      request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second)
    (Graph.FanClosedPort.capability (base := fixedPackedInput ctx)
      request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second)
    (Graph.FanClosedPort.input (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline)
    (ledger.previous.targetResult request) <| by
      exact ledger.added.terminal request

noncomputable def fanClosedPortChargeResidualAt
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (stage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx source))
    (request : FanClosedPortRequest ctx) :=
  fanClosedPortChargeResidual ctx stage.output request

theorem fanClosedPortTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct9)
      (Source := Ledger) (fanClosedPortFamily ctx).executableInterface
      (fanClosedPortAdapter ctx)).profileId =
        "CT9.residual.accumulatedLedger->CT5" :=
  Routes.Accumulated.transition_profile_id
    (fanClosedPortFamily ctx).executableInterface
    (fanClosedPortAdapter ctx)

/-- The next branch-local output determined by the exact preceding prefix.
The bounded branch adds no CT stage; the routed branch retains the entire
incoming CT9 residual inside the new CT5 ledger. -/
noncomputable def FanClosedPortStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularCrossShoulderPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, crossContinuation⟩ =>
      Core.Routing.ResidualStage .ct5
        (FanClosedPortLedger ctx crossContinuation)

/-- One accumulated proof-prefix extension.  This replaces the legacy
constructor that restated every hidden predecessor field. -/
abbrev VerifiedFanClosedPortPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTriangularCrossShoulderPrefix ctx)
    (FanClosedPortStep ctx)

noncomputable def verifiedFanClosedPortPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularCrossShoulderPrefix ctx) :
    VerifiedFanClosedPortPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩, landingContinuation⟩, crossContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanClosedPortLedgerStage ctx crossContinuation⟩

theorem exists_verifiedFanClosedPortPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedFanClosedPortPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTriangularCrossShoulderPrefix object baseline avoids
  exact ⟨ctx, verifiedFanClosedPortPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
