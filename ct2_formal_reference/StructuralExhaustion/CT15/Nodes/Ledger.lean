import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.Ledger
abbrev Contract (F : Framework) (input : Input F) {rank : RankState F input}
    (full : FullRankState F input rank) := LedgerState F input full
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {rank} (full : FullRankState F input rank), Contract F input full
def run {F : Framework} {input : Input F} (plan : Plan F input) {rank : RankState F input}
    (full : FullRankState F input rank) : Contract F input full := plan.certify full
end StructuralExhaustion.CT15.Nodes.Ledger
