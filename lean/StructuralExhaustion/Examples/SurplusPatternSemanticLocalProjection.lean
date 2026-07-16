import StructuralExhaustion.Examples.OrderedBFSTree
import StructuralExhaustion.Graph.LocalSeparatorProjection

namespace StructuralExhaustion.Examples

open StructuralExhaustion

namespace OrderedBFSTreeBranch

/-! Non-Erdős execution of the exact cubic-switch projection. -/

def cubicProjection :
    Graph.LocalSeparatorProjection.Cubic object cubicStar :=
  Graph.LocalSeparatorProjection.cubic object cubicStar

example : cubicProjection.shape =
    Graph.CubicStar.Data.switchBoundaryShape object cubicStar :=
  cubicProjection.shapeExact

example :
    ({cubicProjection.shape.internalVertex} ∪
        Set.range cubicProjection.shape.boundaryVertex) =
      (Graph.CubicStar.Data.support object cubicStar : Set Vertex) :=
  cubicProjection.supportExact

end OrderedBFSTreeBranch

namespace OrderedBFSTreeK5

/-! Non-Erdős execution of the actual high-centre port schedule. -/

def highProjection : Graph.LocalSeparatorProjection.High object 0
    (by native_decide) :=
  Graph.LocalSeparatorProjection.high object 0 (by native_decide)

example : highProjection.ports = Graph.HighCenterPort.ports object 0 :=
  highProjection.portsExact

example : highProjection.ports.card = 4 := by
  rw [highProjection.cardExact]
  native_decide

example : 4 ≤ highProjection.ports.card :=
  highProjection.atLeastFour

end OrderedBFSTreeK5

end StructuralExhaustion.Examples
