import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Arithmetic
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (repeated : RepeatedState F input block) where
  | close (certificate : C1Certificate F input repeated)
  | residual (payload : CT14Payload F input repeated)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (repeated : RepeatedState F input block) := Decision F input repeated
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {scope} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (repeated : RepeatedState F input block),
    Contract F input repeated
def run {F : Framework} {input : Input F} (plan : Plan F input) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    (repeated : RepeatedState F input block) : Contract F input repeated := plan.decide repeated
end StructuralExhaustion.CT17.Nodes.Arithmetic
