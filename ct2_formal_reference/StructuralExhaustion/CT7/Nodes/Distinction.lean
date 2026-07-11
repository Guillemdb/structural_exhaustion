import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Distinction
inductive Decision (F : Framework) (input : Input F)
    {context : ContextState F input}
    (unrealized : UnrealizedState F input context) where
  | defect (state : DefectState F input unrealized)
  | neutral (state : NeutralState F input unrealized)
abbrev Contract (F : Framework) (input : Input F)
    {context : ContextState F input}
    (unrealized : UnrealizedState F input context) := Decision F input unrealized
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {context} (unrealized : UnrealizedState F input context),
    Contract F input unrealized
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {context : ContextState F input} (unrealized : UnrealizedState F input context) :
    Contract F input unrealized := plan.decide unrealized
end StructuralExhaustion.CT7.Nodes.Distinction
