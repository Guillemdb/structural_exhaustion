import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Nodes.Entry

abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input

end StructuralExhaustion.CT5.Nodes.Entry
