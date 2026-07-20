import Erdos64EG.Future.CT1TriangularPortReturn
import StructuralExhaustion.Graph.TriangularFirstLanding
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v w

/-!
# CT10: first landing exhaustion for triangular shoulders

All finite classification, graph semantics, CT1-to-CT10 theorem composition,
trace validity, totality, and the quadratic work certificate are framework
owned.  This module only instantiates that API on the already selected Erdős
graph and retains the exact preceding return prefix.
-/

abbrev TriangularFirstLandingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.TriangularFirstLanding.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh)

noncomputable def triangularFirstLandingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularFirstLandingStage ctx center centerHigh :=
  Graph.TriangularFirstLanding.verifiedStage
    (triangularShoulderSetup ctx center centerHigh)

abbrev TriangularFirstLandingIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  { center : ctx.G.Vertex // 4 ≤ ctx.G.object.degree center }

noncomputable def triangularFirstLandingFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.Routing.PointwiseExecutableFamily .ct10 where
  Index := TriangularFirstLandingIndex ctx
  entry := fun index =>
    (Graph.TriangularFirstLanding.capability
      (triangularShoulderSetup ctx index.1 index.2)).executableInterface
  context := fun index =>
    (Graph.TriangularFirstLanding.input
      (triangularShoulderSetup ctx index.1 index.2)).context
  trigger := fun index =>
    ⟨(Graph.TriangularFirstLanding.input
      (triangularShoulderSetup ctx index.1 index.2)).data⟩

def triangularFirstLandingAdapter {Source : Sort w}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source
      (triangularFirstLandingFamily ctx).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

noncomputable def triangularFirstLandingTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (triangularFirstLandingFamily ctx).executableInterface
    (triangularFirstLandingAdapter ctx) source

abbrev TriangularFirstLandingTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Routes.Accumulated.OutputLedger
    (triangularFirstLandingFamily ctx).executableInterface
    (triangularFirstLandingAdapter ctx) source

abbrev TriangularFirstLandingExecutionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger₅ : Sort v}
    {shoulderStage : Core.Routing.ResidualStage .ct5 Ledger₅}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx shoulderStage)}
    (source : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage)) :=
  Core.Routing.LedgerExtension
    (TriangularFirstLandingTransitionLedger ctx source)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
      TriangularFirstLandingStage ctx center centerHigh)

abbrev TriangularFirstLandingLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger₅ : Sort v}
    {shoulderStage : Core.Routing.ResidualStage .ct5 Ledger₅}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx shoulderStage)}
    (source : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage)) :=
  Core.Routing.LedgerExtension
    (TriangularFirstLandingExecutionLedger ctx source)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
      (port : Graph.TriangularPortReturn.TriPort
        (triangularShoulderSetup ctx center centerHigh)),
      Graph.TriangularFirstLanding.ClassifiedReturnAlternative
        (Graph.TriangularPortReturn.certificate
          (triangularShoulderSetup ctx center centerHigh) port
          (triangularPortRoot ctx bridgeStage center centerHigh port)))

noncomputable def triangularFirstLandingLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger₅ : Sort v}
    {shoulderStage : Core.Routing.ResidualStage .ct5 Ledger₅}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx shoulderStage)}
    (source : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage)) :
    Core.Routing.ResidualStage .ct10
      (TriangularFirstLandingLedger ctx source) := by
  let semanticStage : Core.Routing.ResidualStage .ct10
      (TriangularFirstLandingExecutionLedger ctx source) :=
    (triangularFirstLandingTransitionStage ctx source).extend
      (triangularFirstLandingStage ctx)
  exact semanticStage.extend (fun center centerHigh port =>
    Graph.TriangularFirstLanding.classifyReturn
      (source.output.added center centerHigh port)
      (semanticStage.output.added center centerHigh))

noncomputable def runTriangularFirstLandingCT10
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger₅ : Sort v}
    {shoulderStage : Core.Routing.ResidualStage .ct5 Ledger₅}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx shoulderStage)}
    {source : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage)}
    (stage : Core.Routing.ResidualStage .ct10
      (TriangularFirstLandingLedger ctx source)) :=
  stage.output.previous.previous.targetResult

theorem triangularFirstLandingTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct1)
      (Source := Ledger) (triangularFirstLandingFamily ctx).executableInterface
      (triangularFirstLandingAdapter ctx)).profileId =
        "CT1.residual.accumulatedLedger->CT10" :=
  Routes.Accumulated.transition_profile_id
    (triangularFirstLandingFamily ctx).executableInterface
    (triangularFirstLandingAdapter ctx)

/-- The actual CT1 return from node `[79]` is consumed by the generic graph
composition and its noncentral first completion receives the CT10 class from
node `[80]`. -/
theorem triangularPortReturn_classified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger₅ : Sort v}
    {shoulderStage : Core.Routing.ResidualStage .ct5 Ledger₅}
    {bridgeStage : Core.Routing.ResidualStage .ct2
      (BridgeReductionLedger ctx shoulderStage)}
    (returnStage : Core.Routing.ResidualStage .ct1
      (TriangularPortReturnLedger ctx bridgeStage))
    (landingStage : Core.Routing.ResidualStage .ct10
      (TriangularFirstLandingLedger ctx returnStage))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :
    Graph.TriangularFirstLanding.ClassifiedReturnAlternative
      (Graph.TriangularPortReturn.certificate
        (triangularShoulderSetup ctx center centerHigh) port
        (triangularPortRoot ctx bridgeStage center centerHigh port)) :=
  landingStage.output.added center centerHigh port

noncomputable def TriangularFirstLandingContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularPortReturnPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, returnContinuation⟩ =>
      Core.Routing.ResidualStage .ct10
        (TriangularFirstLandingLedger ctx returnContinuation)

abbrev VerifiedTriangularFirstLandingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTriangularPortReturnPrefix ctx)
    (TriangularFirstLandingContinuation ctx)

noncomputable def verifiedTriangularFirstLandingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularPortReturnPrefix ctx) :
    VerifiedTriangularFirstLandingPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        triangularFirstLandingLedgerStage ctx returnContinuation⟩

theorem exists_verifiedTriangularFirstLandingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTriangularFirstLandingPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTriangularPortReturnPrefix object baseline avoids
  exact ⟨ctx, verifiedTriangularFirstLandingPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
