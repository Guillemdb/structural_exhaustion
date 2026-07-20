import Erdos64EG.Future.CT14HybridFanIncidence
import StructuralExhaustion.Graph.FanWindowCycle
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT1: direct fan-window cycle elimination

The classified hybrid branch enters CT1 through the single accumulated-ledger
transition API.  The target-avoidance proof is a proof-valued trigger, so no
cycle universe is enumerated.  The bounded branch is retained unchanged and
does not acquire a fictitious CT1 edge.
-/

abbrev directFanWindowEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (Graph.FanWindowCycle.encoding (fixedPackedInput ctx)).avoidingExecutableInterface

def directFanWindowAdapter {Source : Sort v}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source (directFanWindowEntry ctx) where
  targetContext := fun _source =>
    (Graph.FanWindowCycle.input (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline ()).context
  trigger := fun _source =>
    ⟨(packedStaticInput.fixedContext ctx).avoids⟩

def directFanWindowTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct14 Ledger) :=
  Routes.Accumulated.advanceCurrent (directFanWindowEntry ctx)
    (directFanWindowAdapter ctx) source

abbrev DirectFanWindowTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct14 Ledger) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct14)
    (directFanWindowEntry ctx) (directFanWindowAdapter ctx) source

/-- Mathematical consequences tied to the literal transitioned CT1 avoiding
run. -/
structure DirectFanWindowFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct14 Ledger}
    (execution : DirectFanWindowTransitionLedger ctx source) : Prop where
  terminal : execution.targetResult.result.terminal = .avoiding
  trace : execution.targetResult.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal]
  checks : execution.targetResult.checks = 0
  directFree : ∀ {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph}
    (pair : Graph.FanWindowCycle.ClosedPair path),
    Graph.FanWindowCycle.DirectCycleFree PowerOfTwoLength pair

abbrev DirectFanWindowLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct14 Ledger) :=
  Core.Routing.LedgerExtension (DirectFanWindowTransitionLedger ctx source)
    (DirectFanWindowFacts ctx)

def directFanWindowLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct14 Ledger) :
    Core.Routing.ResidualStage .ct1 (DirectFanWindowLedger ctx source) :=
  let execution := directFanWindowTransitionStage ctx source
  execution.extend {
    terminal := execution.output.targetResult.terminal_eq
    trace := execution.output.targetResult.trace_eq
    checks := execution.output.targetResult.checks_eq
    directFree := Graph.FanWindowCycle.directCycleFree_of_avoids
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).avoids
  }

def runDirectFanWindowCT1
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct14 Ledger}
    (stage : Core.Routing.ResidualStage .ct1
      (DirectFanWindowLedger ctx source)) :=
  stage.output.previous.targetResult

theorem directFanWindowTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct14)
      (Source := Ledger) (directFanWindowEntry ctx)
      (directFanWindowAdapter ctx)).profileId =
        "CT14.residual.accumulatedLedger->CT1" :=
  Routes.Accumulated.transition_profile_id
    (directFanWindowEntry ctx) (directFanWindowAdapter ctx)

theorem sameWindowPair_directCycleFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct14 Ledger}
    (stage : Core.Routing.ResidualStage .ct1
      (DirectFanWindowLedger ctx source))
    {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph}
    (pair : Graph.FanWindowCycle.ClosedPair path) :
    Graph.FanWindowCycle.DirectCycleFree PowerOfTwoLength pair :=
  stage.output.added.directFree pair

noncomputable def DirectFanWindowStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHybridFanIncidencePrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      _fanContinuation⟩, _massContinuation⟩,
      hybridContinuation⟩ =>
      Core.Routing.ResidualStage .ct1
        (DirectFanWindowLedger ctx hybridContinuation)
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩, _crossContinuation⟩,
      _fanContinuation⟩, _massContinuation⟩,
      _hybridContinuation⟩ => PUnit

abbrev VerifiedDirectFanWindowPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedHybridFanIncidencePrefix ctx)
    (DirectFanWindowStep ctx)

noncomputable def verifiedDirectFanWindowPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHybridFanIncidencePrefix ctx) :
    VerifiedDirectFanWindowPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩, landingContinuation⟩, crossContinuation⟩,
      fanContinuation⟩, massContinuation⟩, hybridContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, massContinuation⟩,
        hybridContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, crossContinuation⟩,
        fanContinuation⟩, massContinuation⟩,
        hybridContinuation⟩,
        directFanWindowLedgerStage ctx hybridContinuation⟩

theorem exists_verifiedDirectFanWindowPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedDirectFanWindowPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedHybridFanIncidencePrefix object baseline avoids
  exact ⟨ctx, verifiedDirectFanWindowPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
