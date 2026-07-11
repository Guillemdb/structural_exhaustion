import StructuralExhaustion.CT3.Types

namespace StructuralExhaustion.CT3.Nodes.Table

inductive Decision (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (persistent : PersistentState F input state) where
  | close (certificate : C5Certificate F input persistent)
  | toCT8 (payload : CT8Payload F input persistent)

abbrev Contract (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (persistent : PersistentState F input state) :=
  Decision F input persistent

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {equivalence} {state : UncompressibleState F input equivalence}
    (persistent : PersistentState F input state), Contract F input persistent

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (persistent : PersistentState F input state) :
    Contract F input persistent :=
  plan.classify persistent

end StructuralExhaustion.CT3.Nodes.Table
