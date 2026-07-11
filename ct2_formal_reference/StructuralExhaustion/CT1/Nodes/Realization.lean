import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Nodes.Realization

inductive Decision (F : Framework) (input : Input F)
    (_equivalence : EquivalenceState F input) where
  | hit (certificate : C1Certificate F input)
  | avoiding (state : AvoidingState F input)

abbrev Contract (F : Framework) (input : Input F)
    (equivalence : EquivalenceState F input) :=
  Decision F input equivalence

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ equivalence : EquivalenceState F input,
    Decision F input equivalence

def run {F : Framework} {input : Input F}
    (plan : Plan F input)
    (equivalence : EquivalenceState F input) :
    Contract F input equivalence :=
  plan.decide equivalence

@[simp] theorem run_eq_decide {F : Framework} {input : Input F}
    (plan : Plan F input)
    (equivalence : EquivalenceState F input) :
    run plan equivalence = plan.decide equivalence := rfl

end StructuralExhaustion.CT1.Nodes.Realization
