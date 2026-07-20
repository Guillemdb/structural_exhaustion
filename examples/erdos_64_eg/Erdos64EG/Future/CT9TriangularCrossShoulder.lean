import Erdos64EG.Future.CT10TriangularFirstLanding
import StructuralExhaustion.Graph.TriangularCrossShoulder
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v w

/-!
# CT9: cross-shoulder multiplicity

The graph layer owns the four-candidate shoulder-pair universe, CT9
partition, high-shoulder/four-cycle proof, bounded survivor, typed trace, and
constant work certificate.  This application retains node `[80]` and
instantiates the generic stage on the selected Erdős graph.
-/

abbrev TriangularCrossShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :=
  Graph.TriangularCrossShoulder.VerifiedStage first second portsNe

def triangularCrossShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :
    TriangularCrossShoulderStage ctx center centerHigh first second portsNe :=
  Graph.TriangularCrossShoulder.verifiedStage first second portsNe

/-- Proof-indexed ordered shoulder-pair requests.  The family is evaluated as
a dependent function and never enumerates centres or pairs. -/
structure TriangularCrossShoulderIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  center : ctx.G.Vertex
  centerHigh : 4 ≤ ctx.G.object.degree center
  first : Graph.TriangularCrossShoulder.TriPort
    (triangularShoulderSetup ctx center centerHigh)
  second : Graph.TriangularCrossShoulder.TriPort
    (triangularShoulderSetup ctx center centerHigh)
  portsNe : first ≠ second

noncomputable def triangularCrossShoulderFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.Routing.PointwiseExecutableFamily .ct9 where
  Index := TriangularCrossShoulderIndex ctx
  entry := fun index =>
    (Graph.TriangularCrossShoulder.capability index.first index.second
      ).executableInterface
  context := fun index =>
    (Graph.TriangularCrossShoulder.input index.first index.second).context
  trigger := fun index =>
    ⟨(Graph.TriangularCrossShoulder.input
      index.first index.second).items⟩

def triangularCrossShoulderAdapter {Source : Sort w}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source
      (triangularCrossShoulderFamily ctx).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

noncomputable def triangularCrossShoulderTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (triangularCrossShoulderFamily ctx).executableInterface
    (triangularCrossShoulderAdapter ctx) source

abbrev TriangularCrossShoulderTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Routes.Accumulated.OutputLedger
    (triangularCrossShoulderFamily ctx).executableInterface
    (triangularCrossShoulderAdapter ctx) source

abbrev TriangularCrossShoulderLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Core.Routing.LedgerExtension
    (TriangularCrossShoulderTransitionLedger ctx source)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
      (first second : Graph.TriangularCrossShoulder.TriPort
        (triangularShoulderSetup ctx center centerHigh))
      (portsNe : first ≠ second),
      TriangularCrossShoulderStage ctx center centerHigh first second portsNe)

noncomputable def triangularCrossShoulderLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :
    Core.Routing.ResidualStage .ct9
      (TriangularCrossShoulderLedger ctx source) :=
  (triangularCrossShoulderTransitionStage ctx source).extend
    (triangularCrossShoulderStage ctx)

noncomputable def runTriangularCrossShoulderCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct10 Ledger}
    (stage : Core.Routing.ResidualStage .ct9
      (TriangularCrossShoulderLedger ctx source)) :=
  stage.output.previous.targetResult

theorem triangularCrossShoulderTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct10)
      (Source := Ledger) (triangularCrossShoulderFamily ctx).executableInterface
      (triangularCrossShoulderAdapter ctx)).profileId =
        "CT10.residual.accumulatedLedger->CT9" :=
  Routes.Accumulated.transition_profile_id
    (triangularCrossShoulderFamily ctx).executableInterface
    (triangularCrossShoulderAdapter ctx)

/-- Exact manuscript state stratification projected from the theorem attached
to the literal CT9 execution ledger. -/
theorem triangularCrossShoulder_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct10 Ledger}
    (stage : Core.Routing.ResidualStage .ct9
      (TriangularCrossShoulderLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :
    Graph.TriangularCrossShoulder.HighShoulder first second ∨
      CT9.fibreCount (Graph.TriangularCrossShoulder.capability first second)
        (Graph.TriangularCrossShoulder.input first second) () ≤ 1 :=
  (stage.output.added center centerHigh first second portsNe).stateSpace

noncomputable def TriangularCrossShoulderContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularFirstLandingPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      _landingContinuation⟩ => PUnit
  | ⟨⟨⟨⟨⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩, _triangularShoulderContinuation⟩,
      _bridgeContinuation⟩, _returnContinuation⟩,
      landingContinuation⟩ =>
      Core.Routing.ResidualStage .ct9
        (TriangularCrossShoulderLedger ctx landingContinuation)

abbrev VerifiedTriangularCrossShoulderPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTriangularFirstLandingPrefix ctx)
    (TriangularCrossShoulderContinuation ctx)

noncomputable def verifiedTriangularCrossShoulderPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularFirstLandingPrefix ctx) :
    VerifiedTriangularCrossShoulderPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩,
      triangularShoulderContinuation⟩, bridgeContinuation⟩,
      returnContinuation⟩, landingContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, triangularShoulderContinuation⟩,
        bridgeContinuation⟩, returnContinuation⟩,
        landingContinuation⟩,
        triangularCrossShoulderLedgerStage ctx landingContinuation⟩

theorem exists_verifiedTriangularCrossShoulderPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTriangularCrossShoulderPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTriangularFirstLandingPrefix object baseline avoids
  exact ⟨ctx, verifiedTriangularCrossShoulderPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
