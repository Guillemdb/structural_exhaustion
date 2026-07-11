import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Block
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    (compatible : CompatibleState F input scope) := BlockState F input compatible
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {scope} (compatible : CompatibleState F input scope), Contract F input compatible
def run {F : Framework} {input : Input F} (plan : Plan F input) {scope : ScopedState F input}
    (compatible : CompatibleState F input scope) : Contract F input compatible :=
  plan.certify compatible
end StructuralExhaustion.CT17.Nodes.Block
