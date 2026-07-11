import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Nodes.Assignment

abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → AssignmentState F input

structure Plan (F : Framework) (input : Input F) where
  certify : Contract F input

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : ScopedState F input) :
    AssignmentState F input := plan.certify state

end StructuralExhaustion.CT4.Nodes.Assignment
