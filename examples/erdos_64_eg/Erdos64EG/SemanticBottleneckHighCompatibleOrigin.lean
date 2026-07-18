import Erdos64EG.SemanticBottleneckDetailedSeparator
import StructuralExhaustion.Graph.SurplusPatternHighCompatibleOrigin

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

namespace Semantic
namespace HighCompatibleOrigin
export Graph.HighCompatiblePortOrigin
  (OpenCompatibleOrigin TriangularCompatibleResidual Outcome
    AssignmentFrontier AssignedEntry assignmentFrontier classify)
export Graph.SurplusPatternHighCompatibleOrigin
  (RootCompatibleLeaf AfterEdgeCompatibleLeaf classifyRoot classifyAfterEdge
    classifyRoot_total classifyAfterEdge_total)
end HighCompatibleOrigin
end Semantic

/-!
# Exact high-compatible origin after the detailed separator

This file is deliberately a thin application boundary.  The graph layer
refines a compatible raw pair to an open-compatible origin or a triangular
residual and retains the root/after-edge incidence source.  The open outcome
exposes the exact assigned-profile premise required by the manuscript; this
file does not manufacture that premise from the unrelated node-[64] support.
-/

variable {V : Type u} {object : Graph.FiniteObject V} {center : V}
variable {centerHigh : 4 ≤ object.degree center}
variable {deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3}
variable {first second : Graph.HighCenterPort.Port object center}

example (origin : Graph.HighCompatiblePortOrigin.OpenCompatibleOrigin object
    center centerHigh deletionCritical first second) :
    (Graph.FanClosedPort.carriers centerHigh deletionCritical origin.firstPort
      origin.secondPort).Nodup :=
  origin.carriers_nodup

example (origin : Graph.HighCompatiblePortOrigin.OpenCompatibleOrigin object
    center centerHigh deletionCritical first second) :
    Graph.HighCompatiblePortOrigin.AssignmentFrontier object center centerHigh
      deletionCritical first second :=
  Graph.HighCompatiblePortOrigin.assignmentFrontier object center centerHigh
    deletionCritical origin

/-! The exact conditional endpoint of the currently verified high-compatible
slice.  Once the manuscript's assigned fan-window entry is supplied, the two
literal recovered ports are fan-closed.  Keeping `entry` explicit is
intentional: neither the pairwise separator clause nor local compatibility
constructs its profile or its six assignment facts. -/

theorem assignedOpenPair_fanClosed
    {frontier : Graph.HighCompatiblePortOrigin.AssignmentFrontier object center
      centerHigh deletionCritical first second}
    (entry : Graph.HighCompatiblePortOrigin.AssignedEntry object center
      centerHigh deletionCritical frontier) :
    Graph.FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
        frontier.origin.firstPort ∧
      Graph.FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
        frontier.origin.secondPort :=
  ⟨Graph.HighCompatiblePortOrigin.AssignedEntry.first_fanClosed object center entry,
    Graph.HighCompatiblePortOrigin.AssignedEntry.second_fanClosed object center entry⟩

end Erdos64EG.Internal
