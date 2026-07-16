import StructuralExhaustion.Core.LocalFiniteCapacity

namespace StructuralExhaustion.Examples.LocalFiniteCapacity

open StructuralExhaustion.Core

example : [2, 4].length ≤ [1, 2, 3, 4].length := by
  apply LocalFiniteCapacity.nodup_length_le_of_mem (by decide)
  intro item member
  simp at member ⊢
  omega

end StructuralExhaustion.Examples.LocalFiniteCapacity
