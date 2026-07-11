import StructuralExhaustion.CT16.Types
namespace StructuralExhaustion.CT16.Nodes.Support
inductive Decision (F : Framework) (input : Input F) where
  | proper {state : ProperState F input} (payload : CT3Payload F input state)
  | whole (state : WholeState F input)
abbrev Contract (F : Framework) (input : Input F) := Decision F input
structure Plan (F : Framework) (input : Input F) where decide : Contract F input
def run {F : Framework} {input : Input F} (_entry : Input F) (plan : Plan F input) :
    Contract F input := plan.decide
end StructuralExhaustion.CT16.Nodes.Support
