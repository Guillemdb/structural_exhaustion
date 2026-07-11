import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Decrease
abbrev Contract (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} {next : Nat}
    (restored : RestoredState F input peeled next) := DecreasedState F input restored
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {load} {state : LoopState F input load}
    {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
    {next : Nat} (restored : RestoredState F input peeled next), Contract F input restored
def run {F : Framework} {input : Input F} (plan : Plan F input) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} {next : Nat}
    (restored : RestoredState F input peeled next) : Contract F input restored :=
  plan.certify restored
end StructuralExhaustion.CT12.Nodes.Decrease
