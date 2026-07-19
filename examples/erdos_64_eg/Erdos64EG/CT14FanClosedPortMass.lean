import Erdos64EG.CT5FanClosedPort
import StructuralExhaustion.Graph.FanClosedPortMass

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT14: actual cubic-closed fan mass

The framework-owned CT5→CT14 route consumes the preceding charge residual.
The Erdős layer supplies only its literal `P₁₃` window/remainder profile and
the Type-B assignment predicate.  CT14 scans the actual semantic subtype of
cubic-closed neighbours and derives the positive quarter-deficit numerator.
-/

abbrev FanClosedMassStage
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
  Graph.FanClosedPortMass.VerifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

noncomputable def fanClosedMassStage
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
    FanClosedMassStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned :=
  Graph.FanClosedPortMass.verifiedStage centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

/-- The graph-local CT5 charge residual selected at one request.  Its value is
read from the accumulated fan-closure ledger; it is never reconstructed from
the request's assignment proof. -/
abbrev FanClosedMassSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : FanClosedPortRequest ctx) :=
  CT5.ChargeLedgerResidual
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

/-- CT14 capability attached to one proof-selected fan-closure request. -/
noncomputable def fanClosedMassCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : FanClosedPortRequest ctx) :=
  Graph.FanClosedPortMass.capability
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (center := request.center)
    (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)

/-- The unique specialized CT5-charge-to-CT14 transition at one request. -/
noncomputable def fanClosedMassTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : FanClosedPortRequest ctx) :=
  Routes.CT5ToCT14.transition
    (S := Graph.FanClosedPort.spec (base := fixedPackedInput ctx)
      request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second)
    (sourceCapability := Graph.FanClosedPort.capability
      (base := fixedPackedInput ctx) request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second)
    (input := Graph.FanClosedPort.input (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline)
    (fanClosedMassCapability ctx request)

/-- Every local CT5→CT14 transition shares the complete CT5 fan ledger.
The family is pointwise: `FanClosedPortRequest` is never enumerated. -/
noncomputable def fanClosedMassTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (crossStage : Core.Routing.ResidualStage .ct9 Ledger) :
    Core.Routing.PointwiseTransitionFamily .ct5 .ct14
      (FanClosedPortLedger ctx crossStage) where
  Index := FanClosedPortRequest ctx
  Source := FanClosedMassSource ctx
  target := fun request => (fanClosedMassCapability ctx request).executableInterface
  transition := fanClosedMassTransition ctx
  current := fun request ledger => fanClosedPortChargeResidual ctx ledger request
  seed := fun _request _source => ()
  discovered := fun _request _source => rfl

noncomputable def fanClosedMassTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    (source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)) :=
  Routes.Accumulated.advanceSelectedPointwise
    (fanClosedMassTransitionFamily ctx crossStage) source

abbrev FanClosedMassTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    (source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)) :=
  Routes.Accumulated.SelectedPointwiseOutputLedger
    (fanClosedMassTransitionFamily ctx crossStage) source

abbrev FanClosedMassStageAtRequest
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : FanClosedPortRequest ctx)
    (execution : CT14.ExecutionResult (fanClosedMassCapability ctx request)
      (Graph.FanClosedPortMass.context (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline)) :=
  Graph.FanClosedPortMass.VerifiedExecutionStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    request.centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
    request.first request.second request.pair request.assigned execution

abbrev FanClosedMassLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    (source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)) :=
  Core.Routing.LedgerExtension
    (FanClosedMassTransitionLedger ctx source)
    (fun execution => ∀ request : FanClosedPortRequest ctx,
      FanClosedMassStageAtRequest ctx request
        (execution.localStage request).targetResult)

/-- The actual pointwise specialized CT5→CT14 execution, extended only by
the graph semantics proved for the same requests. -/
noncomputable def fanClosedMassLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    (source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)) :
    Core.Routing.ResidualStage .ct14 (FanClosedMassLedger ctx source) := by
  let execution := fanClosedMassTransitionStage ctx source
  exact execution.ledgerStage.extend (fun request =>
    Graph.FanClosedPortMass.verifiedExecutionStage request.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.Assigned request.assignedDecidable)
      request.first request.second request.pair request.assigned
      (source.output.added.stage request)
      (execution.localStage request).targetResult rfl)

/-- Literal CT14 result at one request, projected from the specialized local
stage retained by the shared ledger. -/
noncomputable def runFanClosedMassCT14
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (stage : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx source))
    (request : FanClosedPortRequest ctx) :=
  (stage.output.previous.localStage request).targetResult

def fanClosedMassStageAt
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {source : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (stage : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx source))
    (request : FanClosedPortRequest ctx) :
    FanClosedMassStageAtRequest ctx request
      (stage.output.previous.localStage request).targetResult :=
  stage.output.added request

theorem fanClosedMassTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : FanClosedPortRequest ctx) :
    (fanClosedMassTransition ctx request).profileId =
      "CT5.residual.chargeLedger->CT14" :=
  Routes.CT5ToCT14.transition_profile_id
    (fanClosedMassCapability ctx request)

/-- Branch-local CT14 output indexed by the exact accumulated CT5 prefix. -/
noncomputable def FanClosedMassStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedPortPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      _fanContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      fanContinuation⟩ =>
      Core.Routing.ResidualStage .ct14
        (FanClosedMassLedger ctx fanContinuation)

abbrev VerifiedFanClosedMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedFanClosedPortPrefix ctx)
    (FanClosedMassStep ctx)

noncomputable def verifiedFanClosedMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedPortPrefix ctx) :
    VerifiedFanClosedMassPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩, landingContinuation⟩, crossContinuation⟩,
      fanContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, fanClosedMassLedgerStage ctx fanContinuation⟩

theorem exists_verifiedFanClosedMassPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedFanClosedMassPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedFanClosedPortPrefix object baseline avoids
  exact ⟨ctx, verifiedFanClosedMassPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
