import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.Enumeration

universe u

/-!
Finite sum accounting over exact Mathlib enumerations.

The theorem below isolates the list permutation and erasure bookkeeping for
the common situation in which a pointwise natural-valued quantity changes at
exactly two distinct enumerated values.
-/

/-- If `after` differs from `before` only by certified losses at two distinct
points, the total sum loses exactly the sum of those two losses. -/
theorem sum_map_add_two_updates {α : Type u}
    (enumeration : FinEnum α)
    (left right : α) (distinct : left ≠ right)
    (before after : α → Nat) (leftLoss rightLoss : Nat)
    (leftUpdate : after left + leftLoss = before left)
    (rightUpdate : after right + rightLoss = before right)
    (unchanged : ∀ value, value ≠ left → value ≠ right →
      after value = before value) :
    (enumeration.orderedValues.map after).sum + leftLoss + rightLoss =
      (enumeration.orderedValues.map before).sum := by
  letI : DecidableEq α := enumeration.decEq
  let withoutLeft := enumeration.orderedValues.erase left
  let rest := withoutLeft.erase right
  have leftMem : left ∈ enumeration.orderedValues := enumeration.mem_orderedValues left
  have rightMem : right ∈ enumeration.orderedValues := enumeration.mem_orderedValues right
  have rightMemWithoutLeft : right ∈ withoutLeft := by
    apply (List.mem_erase_of_ne distinct.symm).mpr
    exact rightMem
  have arranged : enumeration.orderedValues.Perm (left :: right :: rest) := by
    exact (List.perm_cons_erase leftMem).trans
      ((List.perm_cons_erase rightMemWithoutLeft).cons left)
  have withoutLeftNodup : withoutLeft.Nodup :=
    enumeration.nodup_orderedValues.erase left
  have restValues : rest.map after = rest.map before := by
    apply List.map_congr_left
    intro value member
    have rightSplit := (withoutLeftNodup.mem_erase_iff).mp member
    have leftSplit := (enumeration.nodup_orderedValues.mem_erase_iff).mp rightSplit.2
    exact unchanged value leftSplit.1 rightSplit.1
  have afterSum := (arranged.map after).sum_nat
  have beforeSum := (arranged.map before).sum_nat
  simp only [List.map_cons, List.sum_cons] at afterSum beforeSum
  rw [afterSum, beforeSum, restValues]
  omega

end StructuralExhaustion.Core.Enumeration
