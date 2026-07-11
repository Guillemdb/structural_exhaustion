import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Nodes.Scope

inductive Decision (F : Framework) (input : Input F) where
  | exit (candidate : ScopeCandidate F input)
  | ready (state : ScopedState F input)

abbrev Contract (F : Framework) (input : Input F) := Decision F input

structure Plan (F : Framework) (input : Input F) where
  decide : Decision F input

def run {F : Framework} (input : Input F)
    (plan : Plan F input) : Contract F input :=
  plan.decide

@[simp] theorem run_eq_decide {F : Framework} (input : Input F)
    (plan : Plan F input) : run input plan = plan.decide := rfl

end StructuralExhaustion.CT1.Nodes.Scope
