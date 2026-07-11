import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Nodes.Scope
inductive Decision (F : Framework) (input : Input F) where
  | exit (candidate : ScopeCandidate F input) | ready (state : ScopedState F input)
abbrev Contract (F : Framework) (input : Input F) := Decision F input
structure Plan (F : Framework) (input : Input F) where decide : Contract F input
def run {F : Framework} {input : Input F} (_entry : Input F) (plan : Plan F input) :
    Contract F input := plan.decide
end StructuralExhaustion.CT14.Nodes.Scope
