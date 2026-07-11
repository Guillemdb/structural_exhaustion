import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Realization
inductive Decision (F : Framework) (input : Input F)
    (context : ContextState F input) where
  | close (certificate : C1Certificate F input context)
  | unrealized (state : UnrealizedState F input context)
abbrev Contract (F : Framework) (input : Input F)
    (context : ContextState F input) := Decision F input context
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ context, Contract F input context
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (context : ContextState F input) : Contract F input context := plan.decide context
end StructuralExhaustion.CT7.Nodes.Realization
