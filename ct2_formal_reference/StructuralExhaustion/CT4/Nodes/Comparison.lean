import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Nodes.Comparison

inductive Decision (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (bounded : BoundedFibreState F input total) where
  | close (certificate : C4Certificate F input bounded)
  | residual (payload : CT14Payload F input bounded)

abbrev Contract (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (bounded : BoundedFibreState F input total) :=
  Decision F input bounded

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {assignment} {total : TotalAssignmentState F input assignment}
    (bounded : BoundedFibreState F input total), Contract F input bounded

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (bounded : BoundedFibreState F input total) : Contract F input bounded :=
  plan.decide bounded

end StructuralExhaustion.CT4.Nodes.Comparison
