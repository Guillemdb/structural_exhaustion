import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Nodes.PromotedRouting
inductive Decision (F : Framework) (input : Input F)
    {labels : LabelState F input} {missing : MissingState F input labels}
    (promoted : PromotedState F input missing) where
  | toCT3 (payload : PromotedCT3Payload F input promoted)
  | toCT15 (payload : CT15Payload F input promoted)
abbrev Contract (F : Framework) (input : Input F)
    {labels : LabelState F input} {missing : MissingState F input labels}
    (promoted : PromotedState F input missing) := Decision F input promoted
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {labels} {missing : MissingState F input labels}
    (promoted : PromotedState F input missing), Contract F input promoted
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {labels : LabelState F input} {missing : MissingState F input labels}
    (promoted : PromotedState F input missing) : Contract F input promoted :=
  plan.route promoted
end StructuralExhaustion.CT10.Nodes.PromotedRouting
