import StructuralExhaustion.CT13.Types
namespace StructuralExhaustion.CT13.Nodes.Reconciliation
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    (fallback : FallbackState F input unavailable) where
  | reconciled (state : ReconciledState F input fallback)
  | overlap (state : OverlapState F input fallback)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    (fallback : FallbackState F input unavailable) := Decision F input fallback
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {scope} {unavailable : UnavailableState F input scope}
    (fallback : FallbackState F input unavailable), Contract F input fallback
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
    (fallback : FallbackState F input unavailable) : Contract F input fallback :=
  plan.decide fallback
end StructuralExhaustion.CT13.Nodes.Reconciliation
