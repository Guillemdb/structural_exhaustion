import StructuralExhaustion.CT15.Types
namespace StructuralExhaustion.CT15.Nodes.DependenceRouting
inductive Decision (F : Framework) (input : Input F) {rank : RankState F input}
    (dependence : DependenceState F input rank) where
  | toCT3 (payload : CT3Payload F input dependence)
  | toCT7 (payload : CT7Payload F input dependence)
  | toCT16 (payload : CT16Payload F input dependence)
abbrev Contract (F : Framework) (input : Input F) {rank : RankState F input}
    (dependence : DependenceState F input rank) := Decision F input dependence
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {rank} (dependence : DependenceState F input rank), Contract F input dependence
def run {F : Framework} {input : Input F} (plan : Plan F input) {rank : RankState F input}
    (dependence : DependenceState F input rank) : Contract F input dependence :=
  plan.route dependence
end StructuralExhaustion.CT15.Nodes.DependenceRouting
