import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.Routing
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (overlap : OverlapState F input fallback) where
  | toCT9 (payload : CT9Payload F input overlap)
  | toCT14 (payload : CT14Payload F input overlap)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (overlap : OverlapState F input fallback) := Decision F input overlap
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {scope} {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (overlap : OverlapState F input fallback), Contract F input overlap
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (overlap : OverlapState F input fallback) : Contract F input overlap :=
  plan.route overlap
end StructuralExhaustion.CT13.Nodes.Routing
