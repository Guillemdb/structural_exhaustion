import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Nodes.Compression

inductive Decision (F : Framework) (input : Input F)
    (equivalence : EquivalenceState F input) where
  | close (certificate : C2Certificate F input equivalence)
  | residual (state : UncompressibleState F input equivalence)

abbrev Contract (F : Framework) (input : Input F)
    (equivalence : EquivalenceState F input) :=
  Decision F input equivalence

structure Plan (F : Framework) (input : Input F) where
  decide : ∀ equivalence, Contract F input equivalence

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (equivalence : EquivalenceState F input) :
    Contract F input equivalence :=
  plan.decide equivalence

end StructuralExhaustion.CT3.Nodes.Compression
