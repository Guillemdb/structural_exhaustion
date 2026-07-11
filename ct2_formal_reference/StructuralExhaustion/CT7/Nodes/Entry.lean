import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT7.Nodes.Entry
