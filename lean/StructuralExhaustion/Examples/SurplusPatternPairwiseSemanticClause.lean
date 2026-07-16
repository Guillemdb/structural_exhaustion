import StructuralExhaustion.Examples.SurplusPatternFirstSemanticClause
import StructuralExhaustion.Graph.LocalSeparatorPairwiseClause

namespace StructuralExhaustion.Examples

open StructuralExhaustion

namespace OrderedBFSTreeBranch

def cubicPairwiseClause :=
  Graph.LocalSeparatorPairwiseClause.cubic object cubicFirstClause

example {left right : Fin 3} (distinct : left ≠ right) :
    cubicFirstClause.boundary left ≠ cubicFirstClause.boundary right :=
  cubicPairwiseClause.boundaryPairwise distinct

example (index : Fin 3) :
    cubicProjection.shape.internalVertex ≠ cubicFirstClause.boundary index :=
  cubicPairwiseClause.internal_ne_boundary index

end OrderedBFSTreeBranch

namespace OrderedBFSTreeK5

def highPairwiseClause :=
  Graph.LocalSeparatorPairwiseClause.high object highFirstClause

example {left right : Fin 4} (distinct : left ≠ right) :
    Graph.HighCenterPort.endpoint object 0 (highFirstClause.port left) ≠
      Graph.HighCenterPort.endpoint object 0 (highFirstClause.port right) :=
  highPairwiseClause.endpointPairwise distinct

example (index : Fin 4) : 0 ≠
    Graph.HighCenterPort.endpoint object 0 (highFirstClause.port index) :=
  highPairwiseClause.center_ne_endpoint index

end OrderedBFSTreeK5

end StructuralExhaustion.Examples
