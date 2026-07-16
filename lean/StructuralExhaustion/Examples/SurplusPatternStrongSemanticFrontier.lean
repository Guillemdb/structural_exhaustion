import StructuralExhaustion.Examples.SurplusPatternSemanticLocalProjection
import StructuralExhaustion.Graph.LocalSeparatorSemanticFrontier

namespace StructuralExhaustion.Examples

open StructuralExhaustion

namespace OrderedBFSTreeBranch

/-! Non-Erdős cubic payload: CT3 remains an obligation, not a conclusion. -/

def cubicSemanticPending :=
  Graph.LocalSeparatorSemanticFrontier.cubicPending object cubicProjection

example : cubicSemanticPending.retained = cubicProjection :=
  cubicSemanticPending.retainedExact

example : cubicSemanticPending.obligation =
    Graph.LocalSeparatorSemanticFrontier.Obligation.ct3 :=
  cubicSemanticPending.obligationExact

end OrderedBFSTreeBranch

namespace OrderedBFSTreeK5

/-! Non-Erdős high payload: Type B remains an obligation, not a conclusion. -/

def highSemanticPending :=
  Graph.LocalSeparatorSemanticFrontier.highPending object highProjection

example : highSemanticPending.retained = highProjection :=
  highSemanticPending.retainedExact

example : highSemanticPending.obligation =
    Graph.LocalSeparatorSemanticFrontier.Obligation.typeB :=
  highSemanticPending.obligationExact

end OrderedBFSTreeK5

end StructuralExhaustion.Examples
