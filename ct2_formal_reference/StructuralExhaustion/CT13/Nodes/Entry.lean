import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT13.Nodes.Entry
