import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT9.Nodes.Entry
