import Erdos64EG.CT14FanClosedPortMass
import Erdos64EG.CT1HighCenterStructure
import StructuralExhaustion.Graph.HybridFanIncidence

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT14: hybrid window/non-window incidence budget

The framework-owned CT14→CT14 refinement consumes the literal capacity
residual at one proof-selected fan request.  The family is pointwise and never
enumerates centres, assignments, or fans.  Every target result remains attached
to the complete accumulated CT14 ledger.
-/

/-- One local request on the manuscript branch where the marked fan centre has
degree at most eight. -/
structure HybridFanIncidenceRequest
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  fan : FanClosedPortRequest ctx
  degreeLeEight : ctx.G.object.degree fan.center ≤ 8

noncomputable def hybridFanIncidenceCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : HybridFanIncidenceRequest ctx) :=
  Graph.HybridFanIncidence.capability
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (center := request.fan.center)
    (p13FanWindowProfile ctx request.fan.Assigned
      request.fan.assignedDecidable)

/-- The source capacity residual is extracted from the literal local CT14
result stored in the preceding aggregate ledger. -/
noncomputable def hybridFanIncidenceSourceResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (ledger : FanClosedMassLedger ctx fanStage)
    (request : HybridFanIncidenceRequest ctx) :=
  CT14.ExecutionResult.capacityResidual
    (ledger.previous.localStage request.fan).targetResult
    (ledger.added request.fan).terminal

/-- The unique specialized CT14-capacity-to-CT14 transition at one request. -/
noncomputable def hybridFanIncidenceTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : HybridFanIncidenceRequest ctx) :=
  Routes.CT14ToCT14.transition
    (sourceCapability := fanClosedMassCapability ctx request.fan)
    (ctx := Graph.FanClosedPortMass.context (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline)
    (hybridFanIncidenceCapability ctx request)

/-- Every selected local refinement shares the complete preceding CT14
ledger.  `HybridFanIncidenceRequest` is a dependent function index, not a
finite search universe. -/
noncomputable def hybridFanIncidenceTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    (fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)) :
    Core.Routing.PointwiseTransitionFamily .ct14 .ct14
      (FanClosedMassLedger ctx fanStage) where
  Index := HybridFanIncidenceRequest ctx
  Source := fun request => CT14.CapacityResidual
    (fanClosedMassCapability ctx request.fan)
    (Graph.FanClosedPortMass.context (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline)
  target := fun request =>
    (hybridFanIncidenceCapability ctx request).executableInterface
  transition := hybridFanIncidenceTransition ctx
  current := fun request ledger =>
    hybridFanIncidenceSourceResidual ctx ledger request
  seed := fun _request _source => ()
  discovered := fun _request _source => rfl

noncomputable def hybridFanIncidenceTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)) :=
  Routes.Accumulated.advanceSelectedPointwise
    (hybridFanIncidenceTransitionFamily ctx fanStage) source

abbrev HybridFanIncidenceTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)) :=
  Routes.Accumulated.SelectedPointwiseOutputLedger
    (hybridFanIncidenceTransitionFamily ctx fanStage) source

/-- Graph semantics tied simultaneously to the preceding literal mass result
and the new literal hybrid result. -/
abbrev HybridFanIncidenceStageAtRequest
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage))
    (request : HybridFanIncidenceRequest ctx)
    (execution : CT14.ExecutionResult
      (hybridFanIncidenceCapability ctx request)
      (Graph.HybridFanIncidence.context (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline)) :=
  Graph.HybridFanIncidence.VerifiedExecutionStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    request.fan.centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx request.fan.Assigned
      request.fan.assignedDecidable)
    request.fan.first request.fan.second request.fan.pair request.fan.assigned
    (fourCycleFree ctx) request.degreeLeEight
    (source.output.previous.localStage request.fan).targetResult execution

abbrev HybridFanIncidenceLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)) :=
  Core.Routing.LedgerExtension
    (HybridFanIncidenceTransitionLedger ctx source)
    (fun execution => ∀ request : HybridFanIncidenceRequest ctx,
      HybridFanIncidenceStageAtRequest ctx source request
        (execution.localStage request).targetResult)

/-- The real pointwise CT14→CT14 execution followed by graph semantics for
the same literal source and target results. -/
noncomputable def hybridFanIncidenceLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    (source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)) :
    Core.Routing.ResidualStage .ct14
      (HybridFanIncidenceLedger ctx source) := by
  let execution := hybridFanIncidenceTransitionStage ctx source
  exact execution.ledgerStage.extend (fun request =>
    Graph.HybridFanIncidence.verifiedExecutionStage
      request.fan.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx request.fan.Assigned
        request.fan.assignedDecidable)
      request.fan.first request.fan.second request.fan.pair request.fan.assigned
      (fourCycleFree ctx) request.degreeLeEight
      (source.output.previous.localStage request.fan).targetResult
      (source.output.added request.fan)
      (execution.localStage request).targetResult rfl)

noncomputable def runHybridFanIncidenceCT14
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    {source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)}
    (stage : Core.Routing.ResidualStage .ct14
      (HybridFanIncidenceLedger ctx source))
    (request : HybridFanIncidenceRequest ctx) :=
  (stage.output.previous.localStage request).targetResult

def hybridFanIncidenceStageAt
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {crossStage : Core.Routing.ResidualStage .ct9 Ledger}
    {fanStage : Core.Routing.ResidualStage .ct5
      (FanClosedPortLedger ctx crossStage)}
    {source : Core.Routing.ResidualStage .ct14
      (FanClosedMassLedger ctx fanStage)}
    (stage : Core.Routing.ResidualStage .ct14
      (HybridFanIncidenceLedger ctx source))
    (request : HybridFanIncidenceRequest ctx) :
    HybridFanIncidenceStageAtRequest ctx source request
      (stage.output.previous.localStage request).targetResult :=
  stage.output.added request

theorem hybridFanIncidenceTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : HybridFanIncidenceRequest ctx) :
    (hybridFanIncidenceTransition ctx request).profileId =
      "CT14.residual.capacity->CT14" :=
  Routes.CT14ToCT14.transition_profile_id
    (hybridFanIncidenceCapability ctx request)

/-- Branch-local output indexed by the exact preceding mass prefix. -/
noncomputable def HybridFanIncidenceStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedMassPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      _fanContinuation⟩, massContinuation⟩ =>
      Core.Routing.ResidualStage .ct14
        (HybridFanIncidenceLedger ctx massContinuation)
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      _fanContinuation⟩, _massContinuation⟩ => PUnit

abbrev VerifiedHybridFanIncidencePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedFanClosedMassPrefix ctx)
    (HybridFanIncidenceStep ctx)

noncomputable def verifiedHybridFanIncidencePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedMassPrefix ctx) :
    VerifiedHybridFanIncidencePrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩, landingContinuation⟩, crossContinuation⟩,
      fanContinuation⟩, massContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, massContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, massContinuation⟩,
        hybridFanIncidenceLedgerStage ctx massContinuation⟩

theorem exists_verifiedHybridFanIncidencePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedHybridFanIncidencePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedFanClosedMassPrefix object baseline avoids
  exact ⟨ctx, verifiedHybridFanIncidencePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
