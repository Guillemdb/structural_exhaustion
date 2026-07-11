import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Nodes.Availability

inductive Decision (F : Framework) (input : Input F)
    (assignment : AssignmentState F input) where
  | missing (payload : CT13Payload F input assignment)
  | total (state : TotalAssignmentState F input assignment)

abbrev Contract (F : Framework) (input : Input F)
    (assignment : AssignmentState F input) := Decision F input assignment

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ assignment, Contract F input assignment

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (assignment : AssignmentState F input) :
    Contract F input assignment := plan.decide assignment

end StructuralExhaustion.CT4.Nodes.Availability
