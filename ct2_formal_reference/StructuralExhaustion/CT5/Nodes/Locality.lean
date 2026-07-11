import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Nodes.Locality

abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → LocalityState F input

structure Plan (F : Framework) (input : Input F) where
  certify : Contract F input

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : ScopedState F input) :
    LocalityState F input := plan.certify state

end StructuralExhaustion.CT5.Nodes.Locality
