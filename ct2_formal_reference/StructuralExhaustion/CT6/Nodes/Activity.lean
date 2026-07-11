import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Nodes.Activity

inductive Decision (F : Framework) (input : Input F)
    (definition : DefinitionState F input) where
  | active (state : ActiveState F input definition)
  | dormant (state : DormantState F input definition)

abbrev Contract (F : Framework) (input : Input F)
    (definition : DefinitionState F input) := Decision F input definition

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ definition, Contract F input definition

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (definition : DefinitionState F input) :
    Contract F input definition := plan.decide definition

end StructuralExhaustion.CT6.Nodes.Activity
