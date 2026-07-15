import StructuralExhaustion.Core.GreedyMatchingStar

namespace StructuralExhaustion.Examples.GreedyMatchingStar

open StructuralExhaustion

@[implicit_reducible]
def vertices : FinEnum (Fin 4) := inferInstance

def pairs : Core.OrderedCollection
    (Core.Enumeration.OrderedDistinctPair vertices) :=
  (Core.Enumeration.orderedDistinctPairs vertices).toOrderedCollection

theorem pairs_length : pairs.values.length = 6 := by native_decide

/-- The six edges of the textbook complete graph `K₄` contain a matching or
star of size two; the reusable extractor obtains it from one greedy scan. -/
example : Nonempty (Core.GreedyMatchingStar.Pattern vertices pairs 2) := by
  apply Core.GreedyMatchingStar.exists_pattern_of_cap_lt_card
  native_decide

end StructuralExhaustion.Examples.GreedyMatchingStar
