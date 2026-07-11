import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Neutral
inductive Decision (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (neutral : NeutralState F input unrealized) where
  | close (certificate : C2Certificate F input neutral)
  | toCT10 (payload : CT10Payload F input neutral)
  | toCT16 (payload : CT16Payload F input neutral)
abbrev Contract (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (neutral : NeutralState F input unrealized) := Decision F input neutral
structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {context} {unrealized : UnrealizedState F input context}
    (neutral : NeutralState F input unrealized), Contract F input neutral
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (neutral : NeutralState F input unrealized) : Contract F input neutral :=
  plan.classify neutral
end StructuralExhaustion.CT7.Nodes.Neutral
