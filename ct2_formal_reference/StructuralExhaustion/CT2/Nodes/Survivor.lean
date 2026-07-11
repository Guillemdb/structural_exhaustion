import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.Survivor

inductive Decision (F : Framework) (input : Input F)
    (state : SurvivorState F input) where
  | criticality (payload : CriticalityCT10Payload F input state)
  | missingResponse (payload : ResponseCT3Payload F input state)

abbrev Contract (F : Framework) (input : Input F)
    (state : SurvivorState F input) := Decision F input state

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ state : SurvivorState F input, Decision F input state

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : SurvivorState F input) :
    Contract F input state :=
  plan.classify state

@[simp] theorem run_eq_classify {F : Framework} {input : Input F}
    (plan : Plan F input) (state : SurvivorState F input) :
    run plan state = plan.classify state := rfl

end StructuralExhaustion.CT2.Nodes.Survivor
