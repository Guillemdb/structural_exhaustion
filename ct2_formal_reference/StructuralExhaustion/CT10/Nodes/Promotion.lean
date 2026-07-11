import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Nodes.Promotion
abbrev Contract (F : Framework) (input : Input F) {labels : LabelState F input}
    (missing : MissingState F input labels) := PromotedState F input missing
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {labels} (missing : MissingState F input labels), Contract F input missing
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {labels : LabelState F input} (missing : MissingState F input labels) :
    Contract F input missing := plan.certify missing
end StructuralExhaustion.CT10.Nodes.Promotion
