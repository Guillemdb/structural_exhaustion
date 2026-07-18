import StructuralExhaustion.Examples.FiniteExactStateCorridor
import StructuralExhaustion.Graph.WalkPrefixBoundedExchange

namespace StructuralExhaustion.Examples.WalkPrefixBoundedExchange

open StructuralExhaustion

abbrev profile := Examples.FiniteExactStateCorridor.profile

def pathSupport : List (Fin 7) := [0, 1, 2, 3]

theorem every_repeated_support_is_bounded (repetition : profile.Repeated) :
    (Graph.WalkPrefixBoundedExchange.repeatedSupport pathSupport repetition).card ≤
      profile.stateBound + 1 :=
  Graph.WalkPrefixBoundedExchange.repeatedSupport_card_le_stateBound_add_one
    pathSupport repetition

end StructuralExhaustion.Examples.WalkPrefixBoundedExchange
