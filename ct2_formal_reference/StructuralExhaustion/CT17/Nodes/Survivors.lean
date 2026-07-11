import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Survivors
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (finite : FiniteState F input block) where
  | exhausted (certificate : C5Certificate F input finite)
  | persist (payload : CT8Payload F input finite)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (finite : FiniteState F input block) := Decision F input finite
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {scope} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (finite : FiniteState F input block),
    Contract F input finite
def run {F : Framework} {input : Input F} (plan : Plan F input) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (finite : FiniteState F input block) : Contract F input finite := plan.decide finite
end StructuralExhaustion.CT17.Nodes.Survivors
