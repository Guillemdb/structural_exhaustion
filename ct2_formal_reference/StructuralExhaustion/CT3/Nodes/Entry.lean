import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Nodes.Entry

abbrev Contract (F : Framework) := Input F

def run {F : Framework} (input : Input F) : Contract F := input

end StructuralExhaustion.CT3.Nodes.Entry
