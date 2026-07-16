import StructuralExhaustion.Examples.OrderedBFSTree
import StructuralExhaustion.Graph.SurplusPatternSemanticNormalization

namespace StructuralExhaustion.Examples.SurplusPatternSemanticNormalization

open StructuralExhaustion

/-! Concrete non-Erdős transfer of the cubic/high normalization on the
textbook graphs already used by the ordered-BFS example. -/

namespace CompleteK5

open OrderedBFSTreeK5

def branch := Graph.RootIncidence.classify object 0 (by native_decide)
  rootDivergence

example : match Graph.CubicStar.fromRootBranch object rootDivergence branch with
  | .high .. => True
  | _ => False := by
  change True
  trivial

end CompleteK5

namespace BranchingTree

open OrderedBFSTreeBranch

def branch := Graph.RootIncidence.classifyAfterEdge object 2
  (by native_decide) separatorIncidence

def normalized := Graph.CubicStar.fromAfterEdgeBranch object
  separatorIncidence branch

example : match normalized with
  | .cubic .. => True
  | _ => False := by
  change True
  trivial

example : match normalized with
  | .cubic data => (Graph.CubicStar.Data.support object data).card = 4
  | .high _ => False := by
  change (Graph.CubicStar.Data.support object
    (Graph.CubicStar.ofAfterEdge object separatorIncidence (by native_decide))).card = 4
  exact Graph.CubicStar.Data.support_card object _

end BranchingTree

end StructuralExhaustion.Examples.SurplusPatternSemanticNormalization
