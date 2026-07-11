import StructuralExhaustion.CT5.Types

namespace StructuralExhaustion.CT5.Nodes.Summation

abbrev Contract (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    (ledger : LocalLedgerState F input locality) :=
  SummationState F input ledger

structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {locality} (ledger : LocalLedgerState F input locality),
    Contract F input ledger

def run {F : Framework} {input : Input F}
    (plan : Plan F input) {locality : LocalityState F input}
    (ledger : LocalLedgerState F input locality) : Contract F input ledger :=
  plan.certify ledger

end StructuralExhaustion.CT5.Nodes.Summation
