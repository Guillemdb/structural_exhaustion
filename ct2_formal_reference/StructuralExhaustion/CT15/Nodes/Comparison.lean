import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.Comparison
inductive Decision (F : Framework) (input : Input F) {rank : RankState F input}
    {full : FullRankState F input rank} (ledger : LedgerState F input full) where
  | close (certificate : C4Certificate F input ledger)
  | toCT4 (payload : CT4Payload F input ledger)
abbrev Contract (F : Framework) (input : Input F) {rank : RankState F input}
    {full : FullRankState F input rank} (ledger : LedgerState F input full) :=
  Decision F input ledger
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ {rank} {full : FullRankState F input rank}
    (ledger : LedgerState F input full), Contract F input ledger
def run {F : Framework} {input : Input F} (plan : Plan F input) {rank : RankState F input}
    {full : FullRankState F input rank} (ledger : LedgerState F input full) :
    Contract F input ledger := plan.decide ledger
end StructuralExhaustion.CT15.Nodes.Comparison
