import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT16.Nodes.Entry
