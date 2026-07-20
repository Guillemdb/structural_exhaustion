import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAuditBase

namespace Erdos64EG.Internal

open StructuralExhaustion

abbrev p13CrossOne_power_iff :=
  P13CurvatureArithmeticCertificate.crossOne_power_iff

abbrev p13CrossTwo_power_iff :=
  P13CurvatureArithmeticCertificate.crossTwo_power_iff

theorem p13CodeCompatible_iff (shift : Nat) (left right : P13LabelCode) :
    P13CodeCompatible shift left right ↔
      Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength shift
        (p13LabelEquiv left) (p13LabelEquiv right) := by
  simp only [P13CodeCompatible,
    Graph.InducedPathAttachment.Compatible,
    Graph.InducedPathAttachment.mem_decodeCode_iff,
    p13LabelEquiv_apply]
  tauto

theorem p13PositionDistance_eq_sub_of_lt {left right : Fin 13}
    (less : left < right) :
    Graph.InducedPathAttachment.positionDistance left right =
      right.1 - left.1 := by
  simp [Graph.InducedPathAttachment.positionDistance,
    Nat.max_eq_right (Nat.le_of_lt less),
    Nat.min_eq_left (Nat.le_of_lt less)]

theorem p13CodeCompatibleOne_iff (left right : P13LabelCode) :
    P13CodeCompatibleOne left right ↔ P13CodeCompatible 1 left right := by
  let gapLR := @Graph.InducedPathAttachment.and_shift_cross_eq_zero_iff_no_gap 13
  constructor
  · rintro ⟨lr1, rl1, lr5, rl5⟩ leftPos rightPos leftBit rightBit
    rw [p13CrossOne_power_iff]
    have leftMem : leftPos ∈ Graph.InducedPathAttachment.decodeCode left := by
      simpa using leftBit
    have rightMem : rightPos ∈ Graph.InducedPathAttachment.decodeCode right := by
      simpa using rightBit
    rcases lt_trichotomy leftPos rightPos with less | equal | greater
    · have no1 := (gapLR left right 1 (by decide)).1 lr1
          leftPos leftMem rightPos rightMem less
      have no5 := (gapLR left right 5 (by decide)).1 lr5
          leftPos leftMem rightPos rightMem less
      rw [p13PositionDistance_eq_sub_of_lt less]
      exact not_or.mpr ⟨no1, no5⟩
    · subst rightPos
      simp [Graph.InducedPathAttachment.positionDistance]
    · have no1 := (gapLR right left 1 (by decide)).1 rl1
          rightPos rightMem leftPos leftMem greater
      have no5 := (gapLR right left 5 (by decide)).1 rl5
          rightPos rightMem leftPos leftMem greater
      rw [show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt greater]
      exact not_or.mpr ⟨no1, no5⟩
  · intro compatible
    refine ⟨(gapLR left right 1 (by decide)).2 ?_,
      (gapLR right left 1 (by decide)).2 ?_,
      (gapLR left right 5 (by decide)).2 ?_,
      (gapLR right left 5 (by decide)).2 ?_⟩
    · intro leftPos leftMem rightPos rightMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossOne_power_iff,
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro rightPos rightMem leftPos leftMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossOne_power_iff,
        show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro leftPos leftMem rightPos rightMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossOne_power_iff,
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro rightPos rightMem leftPos leftMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossOne_power_iff,
        show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt less]
      omega

theorem p13CodeCompatibleTwo_iff (left right : P13LabelCode) :
    P13CodeCompatibleTwo left right ↔ P13CodeCompatible 2 left right := by
  let gapLR := @Graph.InducedPathAttachment.and_shift_cross_eq_zero_iff_no_gap 13
  let noCommon := @Graph.InducedPathAttachment.and_eq_zero_iff_no_common 13
  constructor
  · rintro ⟨common, lr4, rl4, lr12, rl12⟩ leftPos rightPos leftBit rightBit
    rw [p13CrossTwo_power_iff]
    have leftMem : leftPos ∈ Graph.InducedPathAttachment.decodeCode left := by
      simpa using leftBit
    have rightMem : rightPos ∈ Graph.InducedPathAttachment.decodeCode right := by
      simpa using rightBit
    rcases lt_trichotomy leftPos rightPos with less | equal | greater
    · have no4 := (gapLR left right 4 (by decide)).1 lr4
          leftPos leftMem rightPos rightMem less
      have no12 := (gapLR left right 12 (by decide)).1 lr12
          leftPos leftMem rightPos rightMem less
      rw [p13PositionDistance_eq_sub_of_lt less]
      exact not_or.mpr ⟨by omega, not_or.mpr ⟨no4, no12⟩⟩
    · subst rightPos
      exact False.elim ((noCommon left right).1 common leftPos leftMem rightMem)
    · have no4 := (gapLR right left 4 (by decide)).1 rl4
          rightPos rightMem leftPos leftMem greater
      have no12 := (gapLR right left 12 (by decide)).1 rl12
          rightPos rightMem leftPos leftMem greater
      rw [show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt greater]
      exact not_or.mpr ⟨by omega, not_or.mpr ⟨no4, no12⟩⟩
  · intro compatible
    refine ⟨(noCommon left right).2 ?_,
      (gapLR left right 4 (by decide)).2 ?_,
      (gapLR right left 4 (by decide)).2 ?_,
      (gapLR left right 12 (by decide)).2 ?_,
      (gapLR right left 12 (by decide)).2 ?_⟩
    · intro position leftMem rightMem
      have safe := compatible position position (by simpa using leftMem)
        (by simpa using rightMem)
      apply safe
      rw [p13CrossTwo_power_iff]
      simp [Graph.InducedPathAttachment.positionDistance]
    · intro leftPos leftMem rightPos rightMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossTwo_power_iff,
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro rightPos rightMem leftPos leftMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossTwo_power_iff,
        show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro leftPos leftMem rightPos rightMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossTwo_power_iff,
        p13PositionDistance_eq_sub_of_lt less]
      omega
    · intro rightPos rightMem leftPos leftMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      rw [p13CrossTwo_power_iff,
        show Graph.InducedPathAttachment.positionDistance leftPos rightPos =
          Graph.InducedPathAttachment.positionDistance rightPos leftPos by
            simp [Graph.InducedPathAttachment.positionDistance,
              Nat.max_comm, Nat.min_comm],
        p13PositionDistance_eq_sub_of_lt less]
      omega

end Erdos64EG.Internal
