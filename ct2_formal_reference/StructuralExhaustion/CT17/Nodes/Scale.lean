import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Scale
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} (block : BlockState F input compatible) where
  | finite (state : FiniteState F input block)
  | repeated (state : RepeatedState F input block)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} (block : BlockState F input compatible) :=
  Decision F input block
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {scope} {compatible : CompatibleState F input scope}
    (block : BlockState F input compatible), Contract F input block
def run {F : Framework} {input : Input F} (plan : Plan F input) {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} (block : BlockState F input compatible) :
    Contract F input block := plan.decide block
end StructuralExhaustion.CT17.Nodes.Scale
