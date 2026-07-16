import StructuralExhaustion.Examples.OrderedBFSTree
import StructuralExhaustion.Graph.HighSeparatorPort

namespace StructuralExhaustion.Examples.HighSeparatorPortK5

open StructuralExhaustion

abbrev Vertex := OrderedBFSTreeK5.Vertex
abbrev object := OrderedBFSTreeK5.object

def rootBranch := Graph.RootIncidence.classify object 0 (by native_decide)
  OrderedBFSTreeK5.rootDivergence

noncomputable def rootPorts := Graph.HighSeparatorPort.ofRootBranch? object
  OrderedBFSTreeK5.rootDivergence Unit () rootBranch

example : rootPorts.isSome = true := by
  change true = true
  rfl

theorem rootPorts_populated : rootPorts.isSome := by
  change true = true
  rfl

noncomputable def rootOutput := rootPorts.get rootPorts_populated

example : Graph.HighCenterPort.endpoint object 0 rootOutput.2.leftPort = 3 :=
  rootOutput.2.left_endpoint

example : Graph.HighCenterPort.endpoint object 0 rootOutput.2.rightPort = 4 :=
  rootOutput.2.right_endpoint

example : Graph.HighCenterPort.endpoint object 0 rootOutput.2.thirdPort =
    rootOutput.1.hit.value := rootOutput.2.third_endpoint

example : rootOutput.2.leftPort ≠ rootOutput.2.rightPort :=
  rootOutput.2.left_ne_right

example : rootOutput.2.thirdPort ≠ rootOutput.2.leftPort :=
  rootOutput.2.third_ne_left

example : rootOutput.2.thirdPort ≠ rootOutput.2.rightPort :=
  rootOutput.2.third_ne_right

def afterEdgeIncidence : Graph.RootIncidence.AfterEdge object 0 where
  predecessor := 1
  leftNext := 3
  rightNext := 4
  predecessorAdjacent := by change (0 : Vertex) ≠ 1; decide
  leftAdjacent := by change (0 : Vertex) ≠ 3; decide
  rightAdjacent := by change (0 : Vertex) ≠ 4; decide
  predecessor_ne_left := by decide
  predecessor_ne_right := by decide
  left_ne_right := by decide

def afterEdgeBranch := Graph.RootIncidence.classifyAfterEdge object 0
  (by native_decide) afterEdgeIncidence

noncomputable def afterEdgePorts :=
  Graph.HighSeparatorPort.ofAfterEdgeBranch? object afterEdgeIncidence Unit ()
    afterEdgeBranch

example : afterEdgePorts.isSome = true := by
  change true = true
  rfl

theorem afterEdgePorts_populated : afterEdgePorts.isSome := by
  change true = true
  rfl

noncomputable def afterEdgeOutput := afterEdgePorts.get afterEdgePorts_populated

example : Graph.HighCenterPort.endpoint object 0
    afterEdgeOutput.predecessorPort = 1 :=
  afterEdgeOutput.predecessor_endpoint

example : Graph.HighCenterPort.endpoint object 0 afterEdgeOutput.leftPort = 3 :=
  afterEdgeOutput.left_endpoint

example : Graph.HighCenterPort.endpoint object 0 afterEdgeOutput.rightPort = 4 :=
  afterEdgeOutput.right_endpoint

example : afterEdgeOutput.predecessorPort ≠ afterEdgeOutput.leftPort :=
  afterEdgeOutput.predecessor_ne_left

example : afterEdgeOutput.predecessorPort ≠ afterEdgeOutput.rightPort :=
  afterEdgeOutput.predecessor_ne_right

example : afterEdgeOutput.leftPort ≠ afterEdgeOutput.rightPort :=
  afterEdgeOutput.left_ne_right

example : Graph.HighSeparatorPort.checks = 0 := rfl

end StructuralExhaustion.Examples.HighSeparatorPortK5
