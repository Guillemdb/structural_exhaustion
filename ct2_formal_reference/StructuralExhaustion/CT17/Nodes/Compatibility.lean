import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Compatibility
inductive Decision (F : Framework) (input : Input F) (scope : ScopedState F input) where
  | compatible (state : CompatibleState F input scope)
  | incompatible (state : IncompatibleState F input scope)
abbrev Contract (F : Framework) (input : Input F) (scope : ScopedState F input) :=
  Decision F input scope
structure Plan (F : Framework) (input : Input F) where decide : ∀ scope, Contract F input scope
def run {F : Framework} {input : Input F} (plan : Plan F input) (scope : ScopedState F input) :
    Contract F input scope := plan.decide scope
end StructuralExhaustion.CT17.Nodes.Compatibility
