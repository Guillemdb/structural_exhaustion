import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT10.Nodes.Entry
