import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Nodes.Bounds
abbrev Contract (F : Framework) (input : Input F) := ScopedState F input → BoundsState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (scope : ScopedState F input) : BoundsState F input := plan.certify scope
end StructuralExhaustion.CT14.Nodes.Bounds
