import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Nodes.ActiveLedger

abbrev Contract (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (active : ActiveState F input definition) := CT4Payload F input active

structure Plan (F : Framework) (input : Input F) where
  build : ∀ {definition} (active : ActiveState F input definition),
    Contract F input active

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {definition : DefinitionState F input}
    (active : ActiveState F input definition) : Contract F input active :=
  plan.build active

end StructuralExhaustion.CT6.Nodes.ActiveLedger
