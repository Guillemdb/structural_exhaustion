import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Nodes.Entry

abbrev Contract (F : Framework) := Input F

def run {F : Framework} (input : Input F) : Contract F := input

end StructuralExhaustion.CT6.Nodes.Entry
