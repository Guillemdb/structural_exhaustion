import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Entry
abbrev Contract (F : Framework) := Input F
def run {F : Framework} (input : Input F) : Contract F := input
end StructuralExhaustion.CT12.Nodes.Entry
