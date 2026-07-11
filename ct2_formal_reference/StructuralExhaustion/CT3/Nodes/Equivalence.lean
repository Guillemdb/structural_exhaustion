import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Nodes.Equivalence

abbrev Contract (F : Framework) (input : Input F) :=
  ScopedState F input → EquivalenceState F input

structure Plan (F : Framework) (input : Input F) where
  certify : Contract F input

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : ScopedState F input) :
    EquivalenceState F input :=
  plan.certify state

end StructuralExhaustion.CT3.Nodes.Equivalence
