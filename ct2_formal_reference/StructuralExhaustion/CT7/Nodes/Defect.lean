import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Defect
inductive Decision (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (defect : DefectState F input unrealized) where
  | close (certificate : C3Certificate F input defect)
  | toCT3 (payload : CT3Payload F input defect)
  | toCT12 (payload : CT12Payload F input defect)
abbrev Contract (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (defect : DefectState F input unrealized) := Decision F input defect
structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {context} {unrealized : UnrealizedState F input context}
    (defect : DefectState F input unrealized), Contract F input defect
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (defect : DefectState F input unrealized) : Contract F input defect :=
  plan.classify defect
end StructuralExhaustion.CT7.Nodes.Defect
