import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Nodes.ClosedType
abbrev Contract (F : Framework) (input : Input F) {whole : WholeState F input}
    (scope : ScopedState F input whole) := ClosedTypeState F input scope
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {whole} (scope : ScopedState F input whole), Contract F input scope
def run {F : Framework} {input : Input F} (plan : Plan F input) {whole : WholeState F input}
    (scope : ScopedState F input whole) : Contract F input scope := plan.certify scope
end StructuralExhaustion.CT16.Nodes.ClosedType
