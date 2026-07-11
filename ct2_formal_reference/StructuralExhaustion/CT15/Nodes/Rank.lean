import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.Rank
abbrev Contract (F : Framework) (input : Input F) := ScopedState F input → RankState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input) (scope : ScopedState F input) :
    RankState F input := plan.certify scope
end StructuralExhaustion.CT15.Nodes.Rank
