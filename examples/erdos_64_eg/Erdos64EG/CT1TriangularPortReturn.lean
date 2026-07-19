import Erdos64EG.CT2BridgeContraction
import StructuralExhaustion.Graph.TriangularPortReturn
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v w

/-!
# CT1: triangular-port return

The CT2 bridge stage is consumed through the framework's generic
`BridgeReductionStage.dartReturn` transition.  The graph layer then derives
the shoulder, the simple path in `G-x`, its reconstructed cycle and first
landing, and executes one certificate-driven CT1 check.  This application
adds only the power-of-two length interpretation.
-/

def triangularPortTargetAvoiding
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬Graph.HasCycleWithLength ctx.G.object.graph
      (fixedPackedInput ctx).LengthOK :=
  (packedStaticInput.fixedContext ctx).avoids

noncomputable def triangularPortRoot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :=
  (bridgeReductionStage ctx bridgeStage).dartReturn
    (Graph.TriangularPortReturn.rootDart
      (triangularShoulderSetup ctx center centerHigh) port)

abbrev TriangularPortReturnStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :=
  Graph.TriangularPortReturn.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh) port
    (triangularPortRoot ctx bridgeStage center centerHigh port)
    (triangularPortTargetAvoiding ctx)

noncomputable def triangularPortReturnStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :
    TriangularPortReturnStage ctx bridgeStage center centerHigh port :=
  Graph.TriangularPortReturn.verifiedStage
    (triangularShoulderSetup ctx center centerHigh) port
    (triangularPortRoot ctx bridgeStage center centerHigh port)
    (triangularPortTargetAvoiding ctx)

/-- The manuscript's displayed Mersenne-predecessor exclusion. -/
theorem triangularPortReturn_length_ne
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (exponent : Nat) (lower : 2 ≤ exponent) :
    (Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) port
      (triangularPortRoot ctx bridgeStage center centerHigh port)).path.length ≠
        2 ^ exponent - 2 := by
  intro equality
  apply (triangularPortReturnStage ctx bridgeStage center centerHigh port).lengthExcluded
  change PowerOfTwoLength
    ((Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) port
      (triangularPortRoot ctx bridgeStage center centerHigh port)).path.length + 2)
  rw [powerOfTwoLength_iff]
  refine ⟨exponent, lower, ?_⟩
  have powerLower : 2 ^ 2 ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) lower
  omega

/-- Proof-indexed triangular ports.  No centre or port universe is scanned. -/
structure TriangularPortReturnIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  center : ctx.G.Vertex
  centerHigh : 4 ≤ ctx.G.object.degree center
  port : Graph.TriangularPortReturn.TriPort
    (triangularShoulderSetup ctx center centerHigh)

noncomputable def triangularPortReturnFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :
    Core.Routing.PointwiseExecutableFamily .ct1 where
  Index := TriangularPortReturnIndex ctx
  entry := fun index =>
    Graph.TriangularPortReturn.executableInterface
      (triangularShoulderSetup ctx index.center index.centerHigh) index.port
      (triangularPortRoot ctx bridgeStage index.center index.centerHigh index.port)
  context := fun _index => ()
  trigger := fun _index => ()

def triangularPortReturnAdapter
    {Source : Sort w}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :
    Routes.Accumulated.Adapter Source
      (triangularPortReturnFamily ctx bridgeStage).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

noncomputable def triangularPortReturnTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :=
  Routes.Accumulated.advanceCurrent
    (triangularPortReturnFamily ctx bridgeStage).executableInterface
    (triangularPortReturnAdapter ctx bridgeStage) bridgeStage

abbrev TriangularPortReturnTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :=
  Routes.Accumulated.OutputLedger
    (triangularPortReturnFamily ctx bridgeStage).executableInterface
    (triangularPortReturnAdapter ctx bridgeStage) bridgeStage

abbrev TriangularPortReturnLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :=
  Core.Routing.LedgerExtension
    (TriangularPortReturnTransitionLedger ctx bridgeStage)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
      (port : Graph.TriangularPortReturn.TriPort
        (triangularShoulderSetup ctx center centerHigh)),
      TriangularPortReturnStage ctx bridgeStage center centerHigh port)

noncomputable def triangularPortReturnLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :
    Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage) :=
  (triangularPortReturnTransitionStage ctx bridgeStage).ledgerStage.extend
    (triangularPortReturnStage ctx bridgeStage)

noncomputable def runTriangularPortReturnCT1
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)}
    (stage : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage)) :=
  stage.output.previous.targetResult

theorem triangularPortReturnTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct5 Ledger}
    (bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx source)) :
    (Routes.Accumulated.transition (sourceTactic := .ct2)
      (Source := BridgeReductionLedger ctx source)
      (triangularPortReturnFamily ctx bridgeStage).executableInterface
      (triangularPortReturnAdapter ctx bridgeStage)).profileId =
        "CT2.residual.accumulatedLedger->CT1" :=
  Routes.Accumulated.transition_profile_id
    (triangularPortReturnFamily ctx bridgeStage).executableInterface
    (triangularPortReturnAdapter ctx bridgeStage)

noncomputable def TriangularPortReturnContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBridgeReductionPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      bridgeContinuation⟩ =>
      Core.Routing.ResidualStage .ct1
        (TriangularPortReturnLedger ctx bridgeContinuation)

abbrev VerifiedTriangularPortReturnPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedBridgeReductionPrefix ctx)
    (TriangularPortReturnContinuation ctx)

noncomputable def verifiedTriangularPortReturnPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBridgeReductionPrefix ctx) :
    VerifiedTriangularPortReturnPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩,
        triangularPortReturnLedgerStage ctx bridgeContinuation⟩

theorem exists_verifiedTriangularPortReturnPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTriangularPortReturnPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedBridgeReductionPrefix object baseline avoids
  exact ⟨ctx, verifiedTriangularPortReturnPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
