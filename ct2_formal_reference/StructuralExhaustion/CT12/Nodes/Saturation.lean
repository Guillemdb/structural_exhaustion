import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Saturation
inductive Decision (F : Framework) (input : Input F) {load : Nat}
    (state : LoopState F input load) where
  | close (certificate : C4Certificate F input state)
  | peel (peelable : PeelableState F input state)
abbrev Contract (F : Framework) (input : Input F) {load : Nat}
    (state : LoopState F input load) := Decision F input state
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {load} (state : LoopState F input load), Contract F input state
def run {F : Framework} {input : Input F} (plan : Plan F input) {load : Nat}
    (state : LoopState F input load) : Contract F input state := plan.decide state
end StructuralExhaustion.CT12.Nodes.Saturation
