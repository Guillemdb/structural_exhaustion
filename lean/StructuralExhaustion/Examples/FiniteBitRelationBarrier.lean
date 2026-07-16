import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace StructuralExhaustion.Examples.FiniteBitRelationBarrier

open StructuralExhaustion

/-- A two-label transfer check: length one is the identity relation and
length two is the complete relation. -/
def profile : Core.FiniteBitRelationBarrier.Profile 2 where
  row
    | 1, source => if source.1 = 0 then 0b01#2 else 0b10#2
    | _, _ => 0b11#2

example : profile.safeCount 1 1 = 2 := by native_decide

example : profile.flatCount 1 1 = 2 := by native_decide

example : profile.obstructedCount 1 1 = 0 := by native_decide

example : profile.checks 1 1 ≤ 2 * (2 + 1) ^ 2 :=
  profile.checks_quadratic 1 1

end StructuralExhaustion.Examples.FiniteBitRelationBarrier
