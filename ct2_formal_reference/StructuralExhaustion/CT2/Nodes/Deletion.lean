import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.Deletion

inductive Decision (F : Framework) (input : Input F)
    (_bounded : BoundedState F input) where
  | closes (witness : DeletionWitness F input)
  | critical (state : DeletionCriticalState F input)

abbrev Contract (F : Framework) (input : Input F)
    (bounded : BoundedState F input) := Decision F input bounded

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ bounded : BoundedState F input, Decision F input bounded

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (bounded : BoundedState F input) :
    Contract F input bounded :=
  plan.decide bounded

@[simp] theorem run_eq_decide {F : Framework} {input : Input F}
    (plan : Plan F input) (bounded : BoundedState F input) :
    run plan bounded = plan.decide bounded := rfl

theorem closes_critical_disjoint {F : Framework} {input : Input F}
    (witness : DeletionWitness F input)
    (critical : DeletionCriticalState F input) : False :=
  critical.critical witness

end StructuralExhaustion.CT2.Nodes.Deletion
