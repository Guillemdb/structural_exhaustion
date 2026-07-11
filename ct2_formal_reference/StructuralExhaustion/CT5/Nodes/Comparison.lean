import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Nodes.Comparison

inductive Decision (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (summation : SummationState F input ledger) where
  | close (certificate : C4Certificate F input summation)
  | toCT4 (payload : CT4Payload F input summation)
  | toCT14 (payload : CT14Payload F input summation)

abbrev Contract (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (summation : SummationState F input ledger) :=
  Decision F input summation

structure Plan (F : Framework) (input : Input F) where
  classify : ∀ {locality} {ledger : LocalLedgerState F input locality}
    (summation : SummationState F input ledger), Contract F input summation

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (summation : SummationState F input ledger) : Contract F input summation :=
  plan.classify summation

end StructuralExhaustion.CT5.Nodes.Comparison
