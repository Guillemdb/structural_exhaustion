import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Nodes.Equivalence
abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → EqualityState F input
structure Plan (F : Framework) (input : Input F) where certify : Contract F input
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (scope : ScopedState F input) : EqualityState F input := plan.certify scope
end StructuralExhaustion.CT8.Nodes.Equivalence
