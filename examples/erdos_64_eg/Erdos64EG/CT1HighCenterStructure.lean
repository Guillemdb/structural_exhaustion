import Erdos64EG.CT9SurplusPairs
import StructuralExhaustion.Graph.HighCenterStructure

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

def fourCycleFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬Graph.HasCycleWithLength ctx.G.object.graph
      Graph.HighCenterStructure.FourLength :=
  Graph.HighCenterStructure.fourFree_of_targetAvoiding
    (fixedPackedInput ctx) ctx.G.object powerOfTwoLength_four
    (packedStaticInput.fixedContext ctx).avoids

def runFourCycleAvoidingCT1
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.HighCenterStructure.runAvoiding ctx.G.object (fourCycleFree ctx)

theorem runFourCycleAvoidingCT1_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runFourCycleAvoidingCT1 ctx).result.terminal = .avoiding :=
  Graph.HighCenterStructure.runAvoiding_terminal ctx.G.object (fourCycleFree ctx)

theorem runFourCycleAvoidingCT1_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runFourCycleAvoidingCT1 ctx).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal] :=
  Graph.HighCenterStructure.runAvoiding_trace ctx.G.object (fourCycleFree ctx)

theorem runFourCycleAvoidingCT1_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runFourCycleAvoidingCT1 ctx).checks = 0 :=
  Graph.HighCenterStructure.runAvoiding_checks ctx.G.object (fourCycleFree ctx)

theorem runFourCycleAvoidingCT1_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ run : CT1.CertifiedAvoidingRun
        (Graph.HighCenterStructure.encoding ctx.G.Vertex).spec
        (Graph.HighCenterStructure.input ctx.G.object),
      run.result.terminal = .avoiding ∧
      run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision,
          .avoidingTerminal] :=
  Graph.HighCenterStructure.runAvoiding_total ctx.G.object (fourCycleFree ctx)

def highCenterStructureStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.HighCenterStructure.VerifiedStage ctx.G.object :=
  Graph.HighCenterStructure.verifiedStage ctx.G.object (fourCycleFree ctx)

/-- The induced graph on every high-centre neighbourhood is a matching. -/
theorem highCenter_neighborhood_matching
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {center left middle right : ctx.G.Vertex}
    (centerLeft : ctx.G.object.graph.Adj center left)
    (centerMiddle : ctx.G.object.graph.Adj center middle)
    (centerRight : ctx.G.object.graph.Adj center right)
    (leftMiddle : ctx.G.object.graph.Adj left middle)
    (middleRight : ctx.G.object.graph.Adj middle right) :
    left = right :=
  (highCenterStructureStage ctx).neighborhoodMatching centerLeft centerMiddle
    centerRight leftMiddle middleRight

/-- Distinct nonadjacent neighbours of one centre have no common neighbour
outside that centre. -/
theorem highCenter_nonadjacent_noCommonOutside
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {center left right common : ctx.G.Vertex}
    (leftNeRight : left ≠ right) (commonNeCenter : common ≠ center)
    (centerLeft : ctx.G.object.graph.Adj center left)
    (centerRight : ctx.G.object.graph.Adj center right)
    (leftCommon : ctx.G.object.graph.Adj left common)
    (rightCommon : ctx.G.object.graph.Adj right common) : False :=
  (highCenterStructureStage ctx).noCommonOutside leftNeRight commonNeCenter
    centerLeft centerRight leftCommon rightCommon

abbrev highCenterStructureEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (Graph.HighCenterStructure.encoding ctx.G.Vertex).avoidingExecutableInterface

/-- Mathematical adapter for the internal CT9→CT1 helper execution.  This is
not a manuscript diagram edge and is therefore absent from the web topology,
but its CT execution and label change are still framework-owned. -/
abbrev highCenterStructureAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :
    Routes.Accumulated.Adapter (SurplusPairEnabledStage ctx previous.1)
      (highCenterStructureEntry ctx) where
  targetContext := fun _source =>
    (Graph.HighCenterStructure.input ctx.G.object).context
  trigger := fun _source => ⟨fourCycleFree ctx⟩

abbrev highCenterStructureTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :=
  Routes.Accumulated.transition (sourceTactic := .ct9)
    (highCenterStructureEntry ctx)
    (highCenterStructureAdapter ctx previous)

abbrev HighCenterStructureEnabledStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :=
  Routes.Accumulated.OutputLedger
    (highCenterStructureEntry ctx)
    (highCenterStructureAdapter ctx previous) previous.2.ledgerStage

def highCenterStructureTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :
    HighCenterStructureEnabledStage ctx previous :=
  Routes.Accumulated.advanceCurrent (highCenterStructureEntry ctx)
    (highCenterStructureAdapter ctx previous) previous.2.ledgerStage

/-- Graph consequences attached to the literal helper CT1 execution. -/
structure HighCenterStructureFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedSurplusPairPrefix ctx}
    (stage : HighCenterStructureEnabledStage ctx previous) : Prop where
  terminal : stage.targetResult.result.terminal = .avoiding
  trace : stage.targetResult.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal]
  stage : Graph.HighCenterStructure.VerifiedStage ctx.G.object
  cubicEndpoints : ∀ {center neighbor : ctx.G.Vertex},
    4 ≤ ctx.G.object.degree center →
    ctx.G.object.graph.Adj center neighbor →
    ctx.G.object.degree neighbor = 3

/-- Complete CT1-labelled application prefix. -/
abbrev VerifiedHighCenterStructurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedSurplusPairPrefix ctx =>
    Core.Routing.LedgerExtension
      (HighCenterStructureEnabledStage ctx previous)
      (HighCenterStructureFacts ctx)

abbrev HighCenterStructureLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedHighCenterStructurePrefix ctx) :=
  Core.Routing.LedgerExtension
    (HighCenterStructureEnabledStage ctx verified.1)
    (HighCenterStructureFacts ctx)

def verifiedHighCenterStructurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :
    VerifiedHighCenterStructurePrefix ctx :=
  let transitionStage := highCenterStructureTransitionStage ctx previous
  ⟨previous, ⟨transitionStage, {
    terminal := runFourCycleAvoidingCT1_terminal ctx
    trace := runFourCycleAvoidingCT1_trace ctx
    stage := highCenterStructureStage ctx
    cubicEndpoints := previous.1.cubicEndpoints
  }⟩⟩

/-- Exact CT1 source stage used by the next manuscript transition. -/
def highCenterStructureLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedHighCenterStructurePrefix ctx) :
    Core.Routing.ResidualStage .ct1
      (HighCenterStructureLedger ctx verified) :=
  verified.2.previous.ledgerStage.extend verified.2.added

theorem exists_verifiedHighCenterStructurePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedHighCenterStructurePrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSurplusPairPrefix object baseline avoids
  exact ⟨ctx, verifiedHighCenterStructurePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
