import StructuralExhaustion.CT7.Types
namespace StructuralExhaustion.CT7.Nodes.Context
abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → ContextState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (scope : ScopedState F input) : ContextState F input := plan.certify scope
end StructuralExhaustion.CT7.Nodes.Context
