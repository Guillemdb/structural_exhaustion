import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Peel
abbrev Contract (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} (peelable : PeelableState F input state) :=
  PeeledState F input peelable
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {load} {state : LoopState F input load}
    (peelable : PeelableState F input state), Contract F input peelable
def run {F : Framework} {input : Input F} (plan : Plan F input) {load : Nat}
    {state : LoopState F input load} (peelable : PeelableState F input state) :
    Contract F input peelable := plan.certify peelable
end StructuralExhaustion.CT12.Nodes.Peel
