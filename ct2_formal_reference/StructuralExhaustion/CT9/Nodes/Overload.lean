import StructuralExhaustion.CT9.Types
namespace StructuralExhaustion.CT9.Nodes.Overload
inductive Decision (F : Framework) (input : Input F) (fibre : FibreState F input) where
  | bounded (payload : CT4Payload F input fibre)
  | overloaded (state : OverloadedState F input fibre)
abbrev Contract (F : Framework) (input : Input F) (fibre : FibreState F input) :=
  Decision F input fibre
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ fibre, Contract F input fibre
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (fibre : FibreState F input) : Contract F input fibre := plan.decide fibre
end StructuralExhaustion.CT9.Nodes.Overload
