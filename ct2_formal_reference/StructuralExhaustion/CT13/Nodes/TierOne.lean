import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.TierOne
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    (available : AvailableState F input scope) := TierOneState F input available
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {scope} (available : AvailableState F input scope), Contract F input available
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} (available : AvailableState F input scope) :
    Contract F input available := plan.certify available
end StructuralExhaustion.CT13.Nodes.TierOne
