import StructuralExhaustion.Examples.SurplusPatternStrongSemanticFrontier
import StructuralExhaustion.Graph.LocalSeparatorFirstClause

namespace StructuralExhaustion.Examples

open StructuralExhaustion

namespace OrderedBFSTreeBranch

def cubicFirstClause :=
  Graph.LocalSeparatorFirstClause.cubic object cubicProjection

example (index : Fin 3) : object.graph.Adj
    cubicProjection.shape.internalVertex (cubicFirstClause.boundary index) :=
  cubicFirstClause.boundaryAdjacent index

example : Function.Injective cubicFirstClause.boundary :=
  cubicFirstClause.boundaryInjective

end OrderedBFSTreeBranch

namespace OrderedBFSTreeK5

def highFirstClause :=
  Graph.LocalSeparatorFirstClause.high object 0 (by native_decide) highProjection

example (index : Fin 4) : object.graph.Adj 0
    (Graph.HighCenterPort.endpoint object 0 (highFirstClause.port index)) :=
  highFirstClause.endpointAdjacent index

example : Function.Injective
    (fun index => Graph.HighCenterPort.endpoint object 0
      (highFirstClause.port index)) :=
  highFirstClause.endpointInjective

end OrderedBFSTreeK5

end StructuralExhaustion.Examples
