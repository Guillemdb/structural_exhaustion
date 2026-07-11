import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.TierOneRouting
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {available : AvailableState F input scope} (tierOne : TierOneState F input available) :=
  CT4Payload F input tierOne
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {scope} {available : AvailableState F input scope}
    (tierOne : TierOneState F input available), Contract F input tierOne
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} {available : AvailableState F input scope}
    (tierOne : TierOneState F input available) : Contract F input tierOne :=
  plan.route tierOne
end StructuralExhaustion.CT13.Nodes.TierOneRouting
