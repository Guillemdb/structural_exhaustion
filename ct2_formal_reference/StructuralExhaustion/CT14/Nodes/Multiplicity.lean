import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Nodes.Multiplicity
inductive Decision (F : Framework) (input : Input F) (bounds : BoundsState F input) where
  | unbounded (payload : CT9Payload F input bounds)
  | missingLabel (payload : CT10Payload F input bounds)
  | counted (state : MultiplicityState F input bounds)
abbrev Contract (F : Framework) (input : Input F) (bounds : BoundsState F input) :=
  Decision F input bounds
structure Plan (F : Framework) (input : Input F) where decide : ∀ bounds, Contract F input bounds
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (bounds : BoundsState F input) : Contract F input bounds := plan.decide bounds
end StructuralExhaustion.CT14.Nodes.Multiplicity
