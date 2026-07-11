import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Nodes.Deficit

inductive Decision (F : Framework) (input : Input F)
    (locality : LocalityState F input) where
  | toCT11 (payload : CT11Payload F input locality)
  | ledger (state : LocalLedgerState F input locality)

abbrev Contract (F : Framework) (input : Input F)
    (locality : LocalityState F input) := Decision F input locality

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ locality, Contract F input locality

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (locality : LocalityState F input) :
    Contract F input locality := plan.classify locality

end StructuralExhaustion.CT5.Nodes.Deficit
