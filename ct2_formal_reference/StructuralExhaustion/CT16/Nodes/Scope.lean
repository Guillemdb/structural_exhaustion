import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Nodes.Scope
inductive Decision (F : Framework) (input : Input F) (whole : WholeState F input) where
  | exit (candidate : ScopeCandidate F input)
  | ready (state : ScopedState F input whole)
abbrev Contract (F : Framework) (input : Input F) (whole : WholeState F input) :=
  Decision F input whole
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ whole, Contract F input whole
def run {F : Framework} {input : Input F} (plan : Plan F input) (whole : WholeState F input) :
    Contract F input whole := plan.decide whole
end StructuralExhaustion.CT16.Nodes.Scope
