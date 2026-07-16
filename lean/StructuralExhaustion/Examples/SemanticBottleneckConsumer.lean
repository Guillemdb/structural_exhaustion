import StructuralExhaustion.Examples.OrderedBFSTree
import StructuralExhaustion.Graph.SurplusPatternSemanticConsumer
import StructuralExhaustion.Graph.SeparatorDegree

namespace StructuralExhaustion.Examples.SemanticBottleneckConsumer

open StructuralExhaustion

/-! Non-Erdős transfer of the exact local degree split used by node [178].
The examples use the already declared textbook graphs from the ordered-BFS
fixture and inspect only one supplied separator. -/

example : match
    Graph.SeparatorDegree.classify OrderedBFSTreeK5.object
      (0 : OrderedBFSTreeK5.Vertex) (by native_decide) with
  | .high .. => True
  | _ => False := by
  change True
  trivial

example : match
    Graph.SeparatorDegree.classify OrderedBFSTreeBranch.object
      (2 : OrderedBFSTreeBranch.Vertex) (by native_decide) with
  | .cubic .. => True
  | _ => False := by
  change True
  trivial

example : Graph.SeparatorDegree.checks = 1 := rfl

def k5RootDivergence : Graph.RootIncidence.Divergence
    OrderedBFSTreeK5.object (0 : OrderedBFSTreeK5.Vertex) where
  leftNext := 1
  rightNext := 2
  leftAdjacent := by
    change (0 : OrderedBFSTreeK5.Vertex) ≠ 1
    decide
  rightAdjacent := by
    change (0 : OrderedBFSTreeK5.Vertex) ≠ 2
    decide
  distinct := by decide

example : match
    Graph.RootIncidence.classify OrderedBFSTreeK5.object
      (0 : OrderedBFSTreeK5.Vertex) (by native_decide) k5RootDivergence with
  | .high .. => True
  | _ => False := by
  change True
  trivial

example (incidence : Graph.RootIncidence.Third OrderedBFSTreeK5.object
    (0 : OrderedBFSTreeK5.Vertex) k5RootDivergence) :
    incidence.hit.value ≠ k5RootDivergence.leftNext ∧
      incidence.hit.value ≠ k5RootDivergence.rightNext :=
  ⟨incidence.ne_left, incidence.ne_right⟩

def k5AfterEdge : Graph.RootIncidence.AfterEdge OrderedBFSTreeK5.object
    (0 : OrderedBFSTreeK5.Vertex) where
  predecessor := 1
  leftNext := 2
  rightNext := 3
  predecessorAdjacent := by
    change (0 : OrderedBFSTreeK5.Vertex) ≠ 1
    decide
  leftAdjacent := by
    change (0 : OrderedBFSTreeK5.Vertex) ≠ 2
    decide
  rightAdjacent := by
    change (0 : OrderedBFSTreeK5.Vertex) ≠ 3
    decide
  predecessor_ne_left := by decide
  predecessor_ne_right := by decide
  left_ne_right := by decide

example : match
    Graph.RootIncidence.classifyAfterEdge OrderedBFSTreeK5.object
      (0 : OrderedBFSTreeK5.Vertex) (by native_decide) k5AfterEdge with
  | .high .. => True
  | _ => False := by
  change True
  trivial

end StructuralExhaustion.Examples.SemanticBottleneckConsumer
