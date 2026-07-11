import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT15.Nodes.Entry
