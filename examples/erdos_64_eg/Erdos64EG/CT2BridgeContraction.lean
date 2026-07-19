import Erdos64EG.CT5TriangularShoulderCompletion
import StructuralExhaustion.Graph.PackedBridgeReduction
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT2: bridge-contraction reduction

The framework constructs the contraction and proves strict rank decrease,
minimum-degree preservation, and exact cycle-length transport.  The Erdős
application supplies only its threshold fact `2 ≤ 3` and retains the framework
stage after the preceding verified prefix.
-/

abbrev BridgeReductionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.BridgeReductionStage (by decide) ctx

abbrev BridgeReductionIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.BridgeReductionIndex ctx

/-- One certificate-driven public CT2 run at every supplied hypothetical
bridge; this is a dependent function and does not enumerate darts. -/
abbrev bridgeReductionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.bridgeReductionFamily (by decide) ctx

def bridgeReductionAdapter {Source : Sort v}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source
      (bridgeReductionFamily ctx).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

def bridgeReductionTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (bridgeReductionFamily ctx).executableInterface
    (bridgeReductionAdapter ctx) source

abbrev BridgeReductionTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Routes.Accumulated.OutputLedger
    (bridgeReductionFamily ctx).executableInterface
    (bridgeReductionAdapter ctx) source

abbrev BridgeReductionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Core.Routing.LedgerExtension
    (BridgeReductionTransitionLedger ctx source)
    (fun _execution => BridgeReductionStage ctx)

/-- The real CT5→CT2 execution, extended by the bridgeless certificate
derived from those literal pointwise CT2 runs. -/
def bridgeReductionLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :
    Core.Routing.ResidualStage .ct2 (BridgeReductionLedger ctx source) :=
  let execution := bridgeReductionTransitionStage ctx source
  execution.extend <|
    packedStaticInput.bridgeReductionStageOfExecutions (by decide) ctx
      execution.output.targetResult

/-- Literal dependent CT2 result produced by the transition. -/
def runBridgeReductionCT2
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (stage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :=
  stage.output.previous.targetResult

theorem bridgeReductionTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct5)
      (Source := Ledger) (bridgeReductionFamily ctx).executableInterface
      (bridgeReductionAdapter ctx)).profileId =
        "CT5.residual.accumulatedLedger->CT2" :=
  Routes.Accumulated.transition_profile_id
    (bridgeReductionFamily ctx).executableInterface
    (bridgeReductionAdapter ctx)

def bridgeReductionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (stage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) : BridgeReductionStage ctx :=
  stage.output.added

/-- Global graph consequence of minimality: every dart of the selected
counterexample is non-bridging.  This theorem is deliberately distinct from
`dart_not_bridge`, which projects the same fact from the literal accumulated
node-`[69]` CT2 stage.  Branches whose manuscript provenance does not pass
through node `[69]` use this graph theorem and therefore acquire no artificial
diagram edge. -/
theorem minimality_dart_not_bridge
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  packedStaticInput.not_isBridge (by decide) ctx dart

/-- Every oriented edge of the selected counterexample is non-bridging, as a
projection of the actual accumulated CT2 stage. -/
theorem dart_not_bridge
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (stage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source))
    (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  (bridgeReductionStage ctx stage).bridgeless dart

noncomputable def BridgeReductionContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularShoulderCompletionPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, triangularShoulderContinuation⟩ =>
      Core.Routing.ResidualStage .ct2
        (BridgeReductionLedger ctx triangularShoulderContinuation)

abbrev VerifiedBridgeReductionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTriangularShoulderCompletionPrefix ctx)
    (BridgeReductionContinuation ctx)

noncomputable def verifiedBridgeReductionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularShoulderCompletionPrefix ctx) :
    VerifiedBridgeReductionPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeReductionLedgerStage ctx triangularShoulderContinuation⟩

theorem exists_verifiedBridgeReductionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedBridgeReductionPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTriangularShoulderCompletionPrefix object baseline avoids
  exact ⟨ctx, verifiedBridgeReductionPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
