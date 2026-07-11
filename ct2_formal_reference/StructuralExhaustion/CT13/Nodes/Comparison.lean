import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.Comparison
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (reconciled : ReconciledState F input fallback) := C4Certificate F input reconciled
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {scope} {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (reconciled : ReconciledState F input fallback), Contract F input reconciled
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (reconciled : ReconciledState F input fallback) : Contract F input reconciled :=
  plan.certify reconciled
end StructuralExhaustion.CT13.Nodes.Comparison
