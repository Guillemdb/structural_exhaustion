import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Nodes.Fibre
abbrev Contract (F : Framework) (input : Input F) := ScopedState F input → FibreState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (scope : ScopedState F input) : FibreState F input := plan.certify scope
end StructuralExhaustion.CT9.Nodes.Fibre
