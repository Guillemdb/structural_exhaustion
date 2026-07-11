import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT17.Nodes.Entry
