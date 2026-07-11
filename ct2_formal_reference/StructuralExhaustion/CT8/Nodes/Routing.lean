import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Nodes.Routing
inductive Decision (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    (separating : SeparatingState F input repeated) where
  | toCT3 (payload : CT3Payload F input separating)
  | toCT7 (payload : CT7Payload F input separating)
abbrev Contract (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    (separating : SeparatingState F input repeated) := Decision F input separating
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {equality} {repeated : RepeatedState F input equality}
    (separating : SeparatingState F input repeated), Contract F input separating
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    (separating : SeparatingState F input repeated) : Contract F input separating :=
  plan.route separating
end StructuralExhaustion.CT8.Nodes.Routing
