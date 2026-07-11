import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Nodes.Defect

inductive Decision (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (state : UncompressibleState F input equivalence) where
  | close (certificate : C3Certificate F input state)
  | toCT7 (payload : CT7Payload F input state)
  | toCT12 (payload : CT12Payload F input state)
  | persistent (next : PersistentState F input state)

abbrev Contract (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (state : UncompressibleState F input equivalence) := Decision F input state

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {equivalence} (state : UncompressibleState F input equivalence),
    Contract F input state

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {equivalence : EquivalenceState F input}
    (state : UncompressibleState F input equivalence) :
    Contract F input state :=
  plan.classify state

end StructuralExhaustion.CT3.Nodes.Defect
