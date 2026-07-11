import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.Fallback
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    (unavailable : UnavailableState F input scope) := FallbackState F input unavailable
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {scope} (unavailable : UnavailableState F input scope),
    Contract F input unavailable
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} (unavailable : UnavailableState F input scope) :
    Contract F input unavailable := plan.certify unavailable
end StructuralExhaustion.CT13.Nodes.Fallback
