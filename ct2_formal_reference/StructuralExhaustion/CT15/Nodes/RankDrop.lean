import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.RankDrop
inductive Decision (F : Framework) (input : Input F) (rank : RankState F input) where
  | dependent (state : DependenceState F input rank)
  | full (state : FullRankState F input rank)
abbrev Contract (F : Framework) (input : Input F) (rank : RankState F input) :=
  Decision F input rank
structure Plan (F : Framework) (input : Input F) where decide : ∀ rank, Contract F input rank
def run {F : Framework} {input : Input F} (plan : Plan F input) (rank : RankState F input) :
    Contract F input rank := plan.decide rank
end StructuralExhaustion.CT15.Nodes.RankDrop
