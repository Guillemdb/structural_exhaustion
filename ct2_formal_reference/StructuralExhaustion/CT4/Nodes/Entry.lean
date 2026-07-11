import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Nodes.Entry

abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input

end StructuralExhaustion.CT4.Nodes.Entry
