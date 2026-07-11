import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT14.Nodes.Entry
