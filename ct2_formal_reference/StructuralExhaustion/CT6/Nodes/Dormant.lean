import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Nodes.Dormant

inductive Decision (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (dormant : DormantState F input definition) where
  | close (certificate : C1Certificate F input dormant)
  | toCT3 (payload : CT3Payload F input dormant)
  | toCT7 (payload : CT7Payload F input dormant)
  | toCT9 (payload : CT9Payload F input dormant)
  | toCT10 (payload : CT10Payload F input dormant)

abbrev Contract (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (dormant : DormantState F input definition) := Decision F input dormant

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {definition} (dormant : DormantState F input definition),
    Contract F input dormant

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {definition : DefinitionState F input}
    (dormant : DormantState F input definition) : Contract F input dormant :=
  plan.classify dormant

end StructuralExhaustion.CT6.Nodes.Dormant
