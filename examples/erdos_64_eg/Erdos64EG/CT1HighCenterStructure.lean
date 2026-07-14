import Erdos64EG.CT9SurplusPairs
import StructuralExhaustion.Graph.HighCenterStructure

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

theorem powerOfTwoLength_four : PowerOfTwoLength 4 := by
  exact ⟨⟨2, by decide⟩, by decide, by decide⟩

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

structure VerifiedHighCenterStructurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSurplusPairPrefix ctx
  stage : Graph.HighCenterStructure.VerifiedStage ctx.G.object
  cubicEndpoints : ∀ {center neighbor : ctx.G.Vertex},
    4 ≤ ctx.G.object.degree center →
    ctx.G.object.graph.Adj center neighbor →
    ctx.G.object.degree neighbor = 3

def verifiedHighCenterStructurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPairPrefix ctx) :
    VerifiedHighCenterStructurePrefix ctx where
  previous := previous
  stage := highCenterStructureStage ctx
  cubicEndpoints := previous.previous.cubicEndpoints

theorem exists_verifiedHighCenterStructurePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedHighCenterStructurePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSurplusPairPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedHighCenterStructurePrefix ctx previous⟩

end Erdos64EG.Internal
