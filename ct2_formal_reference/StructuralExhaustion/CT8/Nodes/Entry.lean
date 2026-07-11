import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT8.Nodes.Entry
