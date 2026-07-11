import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Nodes.Equality
inductive Decision (F : Framework) (input : Input F) {whole : WholeState F input}
    {scope : ScopedState F input whole} (closed : ClosedTypeState F input scope) where
  | equal (certificate : C2Certificate F input closed)
  | distinct (payload : CT10Payload F input closed)
abbrev Contract (F : Framework) (input : Input F) {whole : WholeState F input}
    {scope : ScopedState F input whole} (closed : ClosedTypeState F input scope) :=
  Decision F input closed
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {whole} {scope : ScopedState F input whole}
    (closed : ClosedTypeState F input scope), Contract F input closed
def run {F : Framework} {input : Input F} (plan : Plan F input) {whole : WholeState F input}
    {scope : ScopedState F input whole} (closed : ClosedTypeState F input scope) :
    Contract F input closed := plan.decide closed
end StructuralExhaustion.CT16.Nodes.Equality
