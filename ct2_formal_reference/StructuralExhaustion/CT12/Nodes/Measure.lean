import StructuralExhaustion.CT12.Types
namespace StructuralExhaustion.CT12.Nodes.Measure
abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → LoopState F input input.load
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input) (scope : ScopedState F input) :
    LoopState F input input.load := plan.certify scope
end StructuralExhaustion.CT12.Nodes.Measure
