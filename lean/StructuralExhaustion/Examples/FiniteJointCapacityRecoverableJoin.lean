import StructuralExhaustion.Core.FiniteJointCapacity

namespace StructuralExhaustion.Examples.FiniteJointCapacityRecoverableJoin

open StructuralExhaustion.Core

@[implicit_reducible] def boolPairs : FinEnum (Bool × Bool) :=
  FinEnum.ofNodupList
    [(false, false), (false, true), (true, false), (true, true)]
    (by rintro ⟨left, right⟩; cases left <;> cases right <;> simp)
    (by decide)

/-- A non-graph transfer fixture: two exact Boolean schedules are recoverably
joined into their pair code.  It verifies that applications need only supply
the semantic glue and recovery laws; product injectivity and capacity remain
framework-owned. -/
noncomputable def boolPairJoin :
    FiniteJointCapacity.RecoverableJoin Unit () where
  Left := Bool
  Right := Bool
  Global := Bool × Bool
  Code := Bool × Bool
  left := Enumeration.bool.toOrderedCollection
  right := Enumeration.bool.toOrderedCollection
  codes := boolPairs
  glue := Prod.mk
  recoverLeft := Prod.fst
  recoverRight := Prod.snd
  recoverLeft_glue := by simp
  recoverRight_glue := by simp
  code := id
  codeInjectiveOnGlue := by intro _ _ _ _ equal; exact equal

example :
    boolPairJoin.left.values.length * boolPairJoin.right.values.length ≤
      boolPairJoin.codes.card :=
  boolPairJoin.left_mul_right_le_codeCard

/-- The symbolic finite-type API proves the same capacity statement without
supplying either Boolean family as an ordered schedule. -/
noncomputable def boolPairTypeJoin :
    FiniteJointCapacity.RecoverableTypeJoin Unit () where
  Left := Bool
  Right := Bool
  Global := Bool × Bool
  Code := Bool × Bool
  leftFinite := inferInstance
  rightFinite := inferInstance
  codeFinite := inferInstance
  glue := Prod.mk
  recoverLeft := Prod.fst
  recoverRight := Prod.snd
  recoverLeft_glue := by simp
  recoverRight_glue := by simp
  code := id
  codeInjectiveOnGlue := by intro _ _ _ _ equal; exact equal

example : Nat.card Bool * Nat.card Bool ≤ Nat.card (Bool × Bool) :=
  boolPairTypeJoin.card_mul_card_le_codeCard

example : boolPairTypeJoin.checks = 0 := rfl

end StructuralExhaustion.Examples.FiniteJointCapacityRecoverableJoin
