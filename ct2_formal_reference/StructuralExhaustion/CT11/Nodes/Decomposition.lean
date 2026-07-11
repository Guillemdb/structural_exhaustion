import StructuralExhaustion.CT11.Types
namespace StructuralExhaustion.CT11.Nodes.Decomposition
abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → DecompositionState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (scope : ScopedState F input) : DecompositionState F input := plan.certify scope
end StructuralExhaustion.CT11.Nodes.Decomposition
