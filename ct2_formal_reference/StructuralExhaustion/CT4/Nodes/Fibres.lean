import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Nodes.Fibres

inductive Decision (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    (total : TotalAssignmentState F input assignment) where
  | overloaded (payload : CT9Payload F input total)
  | bounded (state : BoundedFibreState F input total)

abbrev Contract (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    (total : TotalAssignmentState F input assignment) :=
  Decision F input total

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {assignment} (total : TotalAssignmentState F input assignment),
    Contract F input total

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {assignment : AssignmentState F input}
    (total : TotalAssignmentState F input assignment) : Contract F input total :=
  plan.decide total

end StructuralExhaustion.CT4.Nodes.Fibres
