import StructuralExhaustion.Core.LocalPrefixTail

namespace StructuralExhaustion.Examples.LocalPrefixTail

open StructuralExhaustion.Core

example : 1 ∈ ([1, 2, 3, 4].take 2) ∨
    1 ∈ ([1, 2, 3, 4].drop 2) :=
  LocalPrefixTail.exhaustive [1, 2, 3, 4] 2 1 (by decide)

example : 4 ∈ ([1, 2, 3, 4].take 2) ∨
    4 ∈ ([1, 2, 3, 4].drop 2) :=
  LocalPrefixTail.exhaustive [1, 2, 3, 4] 2 4 (by decide)

example : ([1, 2, 3, 4].take 2).length ≤ 2 :=
  LocalPrefixTail.prefix_length_le [1, 2, 3, 4] 2

end StructuralExhaustion.Examples.LocalPrefixTail
