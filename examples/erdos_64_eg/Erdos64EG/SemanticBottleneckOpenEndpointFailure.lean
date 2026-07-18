import Erdos64EG.SemanticBottleneckDetailedSeparator
import StructuralExhaustion.Graph.SurplusPatternOpenEndpointFailure
import StructuralExhaustion.Graph.SurplusPatternOpenEndpointBlockerConnector

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace OpenEndpointFailure
export Graph.HighOpenEndpointFailure
  (NormalizedFailure ActivatedFailure classify suppressionSetup activate)
export Graph.SurplusPatternOpenEndpointFailure
  (RootFailureLeaf AfterEdgeFailureLeaf activateRoot activateAfterEdge
    ActivationFrontier SelectedSlotEntry)
end OpenEndpointFailure
namespace OpenEndpointBlockerConnector
export Graph.SurplusPatternOpenEndpointBlockerConnector
  (SlotIdentification PairIdentification ConnectorFrontier frontier
    SharedCandidateWitness execute)
end OpenEndpointBlockerConnector
end Semantic

variable {input : Graph.PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {center : ctx.G.Vertex}
variable {centerHigh : 4 ≤ ctx.G.object.degree center}
variable {deletionCritical : ∀ dart : ctx.G.object.graph.Dart,
  ctx.G.object.degree dart.fst = 3 ∨ ctx.G.object.degree dart.snd = 3}
variable {first second : Graph.HighCenterPort.Port ctx.G.object center}

noncomputable example (minimumDegree_eq_three : input.minimumDegree = 3)
    (failure : Graph.HighSeparatorPortClassification.OpenEndpointFailure
      ctx.G.object center centerHigh deletionCritical first second) :
    Graph.HighOpenEndpointFailure.ActivatedFailure input ctx center centerHigh
      deletionCritical first second :=
  Graph.HighOpenEndpointFailure.activate input ctx minimumDegree_eq_three center
    centerHigh deletionCritical failure

end Erdos64EG.Internal
