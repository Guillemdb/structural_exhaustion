import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Nodes.Direct
inductive Decision (F : Framework) (input : Input F)
    {labels : LabelState F input} (direct : DirectState F input labels) where
  | toCT3 (payload : DirectCT3Payload F input direct)
  | toCT7 (payload : CT7Payload F input direct)
abbrev Contract (F : Framework) (input : Input F)
    {labels : LabelState F input} (direct : DirectState F input labels) :=
  Decision F input direct
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {labels} (direct : DirectState F input labels), Contract F input direct
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {labels : LabelState F input} (direct : DirectState F input labels) :
    Contract F input direct := plan.route direct
end StructuralExhaustion.CT10.Nodes.Direct
