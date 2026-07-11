import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Nodes.Routing
inductive Decision (F : Framework) (input : Input F)
    {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
    (extraction : ExtractionState F input overloaded) where
  | close (certificate : C1Certificate F input extraction)
  | toCT7 (payload : CT7Payload F input extraction)
  | toCT8 (payload : CT8Payload F input extraction)
abbrev Contract (F : Framework) (input : Input F)
    {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
    (extraction : ExtractionState F input overloaded) := Decision F input extraction
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {fibre} {overloaded : OverloadedState F input fibre}
    (extraction : ExtractionState F input overloaded), Contract F input extraction
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {fibre : FibreState F input} {overloaded : OverloadedState F input fibre}
    (extraction : ExtractionState F input overloaded) : Contract F input extraction :=
  plan.route extraction
end StructuralExhaustion.CT9.Nodes.Routing
