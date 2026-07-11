import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.Interface

inductive Decision (F : Framework) (input : Input F) where
  | scope (candidate : ScopeCandidate F input)
  | bounded (state : BoundedState F input)

abbrev Contract (F : Framework) (input : Input F) := Decision F input

structure Plan (F : Framework) (input : Input F) where
  decide : Decision F input

def run {F : Framework} (input : Input F)
    (plan : Plan F input) : Contract F input :=
  plan.decide

@[simp] theorem run_eq_decide {F : Framework} (input : Input F)
    (plan : Plan F input) : run input plan = plan.decide := rfl

theorem scope_bounded_disjoint {F : Framework} {input : Input F}
    (scope : ScopeCandidate F input) (bounded : BoundedState F input) : False :=
  scope.unbounded bounded.bounded

end StructuralExhaustion.CT2.Nodes.Interface
