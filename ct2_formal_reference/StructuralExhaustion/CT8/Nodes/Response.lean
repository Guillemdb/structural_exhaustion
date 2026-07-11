import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Nodes.Response
inductive Decision (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    (repeated : RepeatedState F input equality) where
  | close (certificate : C2Certificate F input repeated)
  | separating (state : SeparatingState F input repeated)
abbrev Contract (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    (repeated : RepeatedState F input equality) := Decision F input repeated
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {equality} (repeated : RepeatedState F input equality),
    Contract F input repeated
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {equality : EqualityState F input} (repeated : RepeatedState F input equality) :
    Contract F input repeated := plan.decide repeated
end StructuralExhaustion.CT8.Nodes.Response
