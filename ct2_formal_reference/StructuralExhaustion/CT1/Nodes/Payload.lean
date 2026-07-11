import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Nodes.Payload

inductive Decision (F : Framework) (input : Input F)
    (avoiding : AvoidingState F input) where
  | toCT2 (payload : CT2Payload F input avoiding)
  | toCT3 (payload : CT3Payload F input avoiding)
  | toCT4 (payload : CT4Payload F input avoiding)
  | toCT5 (payload : CT5Payload F input avoiding)
  | toCT6 (payload : CT6Payload F input avoiding)
  | toCT17 (payload : CT17Payload F input avoiding)

abbrev Contract (F : Framework) (input : Input F)
    (avoiding : AvoidingState F input) :=
  Decision F input avoiding

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ avoiding : AvoidingState F input,
    Decision F input avoiding

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (avoiding : AvoidingState F input) :
    Contract F input avoiding :=
  plan.classify avoiding

@[simp] theorem run_eq_classify {F : Framework} {input : Input F}
    (plan : Plan F input) (avoiding : AvoidingState F input) :
    run plan avoiding = plan.classify avoiding := rfl

end StructuralExhaustion.CT1.Nodes.Payload
