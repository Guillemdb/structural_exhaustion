import StructuralExhaustion.CT17.Types
namespace StructuralExhaustion.CT17.Nodes.Separation
inductive Decision (F : Framework) (input : Input F) {scope : ScopedState F input}
    (state : IncompatibleState F input scope) where
  | toCT3 (payload : CT3Payload F input state)
  | toCT10 (payload : CT10Payload F input state)
abbrev Contract (F : Framework) (input : Input F) {scope : ScopedState F input}
    (state : IncompatibleState F input scope) := Decision F input state
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {scope} (state : IncompatibleState F input scope), Contract F input state
def run {F : Framework} {input : Input F} (plan : Plan F input) {scope : ScopedState F input}
    (state : IncompatibleState F input scope) : Contract F input state := plan.route state
end StructuralExhaustion.CT17.Nodes.Separation
