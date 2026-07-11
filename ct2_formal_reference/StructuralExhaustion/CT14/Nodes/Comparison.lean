import StructuralExhaustion.CT14.Types
namespace StructuralExhaustion.CT14.Nodes.Comparison
abbrev Contract (F : Framework) (input : Input F) {bounds : BoundsState F input}
    (multiplicity : MultiplicityState F input bounds) := C4Certificate F input multiplicity
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {bounds} (multiplicity : MultiplicityState F input bounds),
    Contract F input multiplicity
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {bounds : BoundsState F input} (multiplicity : MultiplicityState F input bounds) :
    Contract F input multiplicity := plan.certify multiplicity
end StructuralExhaustion.CT14.Nodes.Comparison
