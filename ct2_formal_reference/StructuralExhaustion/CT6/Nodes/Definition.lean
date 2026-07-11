import StructuralExhaustion.CT6.Types

namespace StructuralExhaustion.CT6.Nodes.Definition

abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → DefinitionState F input

structure Plan (F : Framework) (input : Input F) where
  certify : Contract F input

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (scope : ScopedState F input) :
    DefinitionState F input := plan.certify scope

end StructuralExhaustion.CT6.Nodes.Definition
