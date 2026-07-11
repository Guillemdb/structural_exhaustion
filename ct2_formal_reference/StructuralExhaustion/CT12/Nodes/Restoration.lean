import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Restoration
inductive Decision (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (peeled : PeeledState F input peelable) where
  | continue {next : Nat} (restored : RestoredState F input peeled next)
  | toCT4 (payload : CT4Payload F input peeled)
  | toCT13 (payload : CT13Payload F input peeled)
abbrev Contract (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (peeled : PeeledState F input peelable) := Decision F input peeled
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {load} {state : LoopState F input load}
    {peelable : PeelableState F input state} (peeled : PeeledState F input peelable),
    Contract F input peeled
def run {F : Framework} {input : Input F} (plan : Plan F input) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (peeled : PeeledState F input peelable) : Contract F input peeled := plan.decide peeled
end StructuralExhaustion.CT12.Nodes.Restoration
