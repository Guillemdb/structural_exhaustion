import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Nodes.Extraction
abbrev Contract (F : Framework) (input : Input F) {fibre : FibreState F input}
    (overloaded : OverloadedState F input fibre) := ExtractionState F input overloaded
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {fibre} (overloaded : OverloadedState F input fibre),
    Contract F input overloaded
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {fibre : FibreState F input} (overloaded : OverloadedState F input fibre) :
    Contract F input overloaded := plan.certify overloaded
end StructuralExhaustion.CT9.Nodes.Extraction
