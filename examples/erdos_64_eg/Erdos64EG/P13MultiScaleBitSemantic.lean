import Erdos64EG.P13CurvatureBitSemantic

namespace Erdos64EG.Internal

open StructuralExhaustion

/-- A uniform bit-vector normal form for compatibility at every connector
scale.  Unlike `P13CodeCompatible`, its executable test scans the thirteen
possible gaps once and performs only word operations. -/
def P13CodeCompatibleFast (shift : Nat) (left right : P13LabelCode) : Prop :=
  (PowerOfTwoLength (shift + 2) → left &&& right = 0#13) ∧
    ∀ gap : Fin 13, 0 < gap.1 →
      PowerOfTwoLength (shift + 2 + gap.1) →
        left &&& (right >>> gap.1) = 0#13 ∧
          right &&& (left >>> gap.1) = 0#13

def p13CodeCompatibleFastDecidable (shift : Nat)
    (left right : P13LabelCode) : Decidable
      (P13CodeCompatibleFast shift left right) := by
  unfold P13CodeCompatibleFast
  infer_instance

/-- On the finite scale range used by node `[21]`, the only relevant powers
of two are 4, 8, and 16.  This arithmetic normal form avoids re-running the
bounded existential search in every matrix cell. -/
def P13SmallPowerGap (shift gap : Nat) : Prop :=
  shift + 2 + gap = 4 ∨ shift + 2 + gap = 8 ∨ shift + 2 + gap = 16

def p13SmallPowerGapDecidable (shift gap : Nat) :
    Decidable (P13SmallPowerGap shift gap) := by
  unfold P13SmallPowerGap
  infer_instance

theorem p13SmallPowerGap_iff (shift gap : Nat)
    (shift_lt : shift < 15) (gap_lt : gap < 13) :
    P13SmallPowerGap shift gap ↔
      PowerOfTwoLength (shift + 2 + gap) := by
  constructor
  · intro small
    unfold P13SmallPowerGap at small
    unfold PowerOfTwoLength
    rcases small with four | eight | sixteen
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · norm_num
      · norm_num
        omega
    · refine ⟨⟨3, by omega⟩, ?_, ?_⟩
      · norm_num
      · norm_num
        omega
    · refine ⟨⟨4, by omega⟩, ?_, ?_⟩
      · norm_num
      · norm_num
        omega
  · rintro ⟨exponent, lower, equality⟩
    have sum_le : shift + 2 + gap ≤ 28 := by omega
    have exponent_lt : exponent.1 < 5 := by
      by_contra not_lt
      have powerLower : 2 ^ 5 ≤ 2 ^ exponent.1 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    unfold P13SmallPowerGap
    interval_cases exponent.1 <;> norm_num at lower equality ⊢ <;> omega

def P13CodeCompatibleBits (shift : Nat) (left right : P13LabelCode) : Prop :=
  (P13SmallPowerGap shift 0 → left &&& right = 0#13) ∧
    ∀ gap : Fin 13, 0 < gap.1 → P13SmallPowerGap shift gap.1 →
      left &&& (right >>> gap.1) = 0#13 ∧
        right &&& (left >>> gap.1) = 0#13

def p13CodeCompatibleBitsDecidable (shift : Nat)
    (left right : P13LabelCode) : Decidable
      (P13CodeCompatibleBits shift left right) := by
  unfold P13CodeCompatibleBits
  letI : DecidablePred (P13SmallPowerGap shift) :=
    p13SmallPowerGapDecidable shift
  infer_instance

theorem p13CodeCompatibleBits_iff (shift : Nat) (shift_lt : shift < 15)
    (left right : P13LabelCode) :
    P13CodeCompatibleBits shift left right ↔
      P13CodeCompatibleFast shift left right := by
  unfold P13CodeCompatibleBits P13CodeCompatibleFast
  constructor
  · rintro ⟨common, gaps⟩
    refine ⟨fun power => common ((p13SmallPowerGap_iff shift 0 shift_lt
      (by decide)).2 (by simpa using power)), ?_⟩
    intro gap positive power
    exact gaps gap positive ((p13SmallPowerGap_iff shift gap.1 shift_lt
      gap.isLt).2 power)
  · rintro ⟨common, gaps⟩
    refine ⟨fun power => common (by
      simpa using (p13SmallPowerGap_iff shift 0 shift_lt (by decide)).1 power), ?_⟩
    intro gap positive power
    exact gaps gap positive
      ((p13SmallPowerGap_iff shift gap.1 shift_lt gap.isLt).1 power)

/-- The actual forbidden gaps at scales below fifteen.  This sparse list is
the executable representation used by the multi-scale certificate. -/
def p13ForbiddenGaps : Nat → List Nat
  | 0 => [2, 6]
  | 1 => [1, 5]
  | 2 => [0, 4, 12]
  | 3 => [3, 11]
  | 4 => [2, 10]
  | 5 => [1, 9]
  | 6 => [0, 8]
  | 7 => [7]
  | 8 => [6]
  | 9 => [5]
  | 10 => [4]
  | 11 => [3]
  | 12 => [2]
  | 13 => [1]
  | 14 => [0]
  | _ => []

theorem mem_p13ForbiddenGaps_iff (shift gap : Nat)
    (shift_lt : shift < 15) (gap_lt : gap < 13) :
    gap ∈ p13ForbiddenGaps shift ↔ P13SmallPowerGap shift gap := by
  interval_cases shift <;>
    simp [p13ForbiddenGaps, P13SmallPowerGap] <;> omega

theorem p13ForbiddenGaps_lt_thirteen (shift gap : Nat)
    (shift_lt : shift < 15) (member : gap ∈ p13ForbiddenGaps shift) :
    gap < 13 := by
  interval_cases shift <;> simp [p13ForbiddenGaps] at member <;> omega

def P13CodeCompatibleSparse (shift : Nat)
    (left right : P13LabelCode) : Prop :=
  ∀ gap ∈ p13ForbiddenGaps shift,
    if gap = 0 then left &&& right = 0#13
    else left &&& (right >>> gap) = 0#13 ∧
      right &&& (left >>> gap) = 0#13

def p13CodeCompatibleSparseDecidable (shift : Nat)
    (left right : P13LabelCode) : Decidable
      (P13CodeCompatibleSparse shift left right) := by
  unfold P13CodeCompatibleSparse
  infer_instance

theorem p13CodeCompatibleSparse_iff (shift : Nat) (shift_lt : shift < 15)
    (left right : P13LabelCode) :
    P13CodeCompatibleSparse shift left right ↔
      P13CodeCompatibleBits shift left right := by
  constructor
  · intro sparse
    refine ⟨fun power => ?_, fun gap positive power => ?_⟩
    · have member : 0 ∈ p13ForbiddenGaps shift :=
        (mem_p13ForbiddenGaps_iff shift 0 shift_lt (by decide)).2 power
      simpa using sparse 0 member
    · have member : gap.1 ∈ p13ForbiddenGaps shift :=
        (mem_p13ForbiddenGaps_iff shift gap.1 shift_lt gap.isLt).2 power
      simpa [Nat.ne_of_gt positive] using sparse gap.1 member
  · rintro ⟨common, gaps⟩ gap member
    have gap_lt := p13ForbiddenGaps_lt_thirteen shift gap shift_lt member
    by_cases zero : gap = 0
    · subst gap
      exact common ((mem_p13ForbiddenGaps_iff shift 0 shift_lt
        (by decide)).1 member)
    · simp only [if_neg zero]
      exact gaps ⟨gap, gap_lt⟩ (Nat.pos_of_ne_zero zero)
        ((mem_p13ForbiddenGaps_iff shift gap shift_lt gap_lt).1 member)

theorem p13CodeCompatibleFast_iff (shift : Nat) (left right : P13LabelCode) :
    P13CodeCompatibleFast shift left right ↔
      P13CodeCompatible shift left right := by
  let gapZero := @Graph.InducedPathAttachment.and_eq_zero_iff_no_common 13
  let gapPositive :=
    @Graph.InducedPathAttachment.and_shift_cross_eq_zero_iff_no_gap 13
  constructor
  · rintro ⟨common, gaps⟩ leftPos rightPos leftBit rightBit power
    have leftMem : leftPos ∈ Graph.InducedPathAttachment.decodeCode left := by
      simpa using leftBit
    have rightMem : rightPos ∈ Graph.InducedPathAttachment.decodeCode right := by
      simpa using rightBit
    rcases lt_trichotomy leftPos rightPos with less | equal | greater
    · have gapBound : rightPos.1 - leftPos.1 < 13 := by omega
      have gapNonzero : 0 < rightPos.1 - leftPos.1 := by omega
      have powerGap : PowerOfTwoLength
          (shift + 2 + (rightPos.1 - leftPos.1)) := by
        simpa [Graph.InducedPathAttachment.crossCycleLength,
          p13PositionDistance_eq_sub_of_lt less] using power
      have zero := (gaps ⟨rightPos.1 - leftPos.1, gapBound⟩ gapNonzero powerGap).1
      exact ((gapPositive left right (rightPos.1 - leftPos.1) gapNonzero).1 zero
        leftPos leftMem rightPos rightMem less) rfl
    · subst rightPos
      exact ((gapZero left right).1 (common (by
        simpa [Graph.InducedPathAttachment.crossCycleLength,
          Graph.InducedPathAttachment.positionDistance] using power))
        leftPos leftMem) rightMem
    · have gapBound : leftPos.1 - rightPos.1 < 13 := by omega
      have gapNonzero : 0 < leftPos.1 - rightPos.1 := by omega
      have distanceSymm :
          Graph.InducedPathAttachment.positionDistance leftPos rightPos =
            Graph.InducedPathAttachment.positionDistance rightPos leftPos := by
        simp [Graph.InducedPathAttachment.positionDistance,
          Nat.max_comm, Nat.min_comm]
      have powerGap : PowerOfTwoLength
          (shift + 2 + (leftPos.1 - rightPos.1)) := by
        simpa [Graph.InducedPathAttachment.crossCycleLength, distanceSymm,
          p13PositionDistance_eq_sub_of_lt greater] using power
      have zero := (gaps ⟨leftPos.1 - rightPos.1, gapBound⟩ gapNonzero powerGap).2
      exact ((gapPositive right left (leftPos.1 - rightPos.1) gapNonzero).1 zero
        rightPos rightMem leftPos leftMem greater) rfl
  · intro compatible
    refine ⟨fun power => (gapZero left right).2 ?_, fun gap positive power => ⟨
      (gapPositive left right gap.1 positive).2 ?_,
      (gapPositive right left gap.1 positive).2 ?_⟩⟩
    · intro position leftMem rightMem
      exact compatible position position (by simpa using leftMem)
        (by simpa using rightMem) (by
          simpa [Graph.InducedPathAttachment.crossCycleLength,
            Graph.InducedPathAttachment.positionDistance] using power)
    · intro leftPos leftMem rightPos rightMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      simpa [Graph.InducedPathAttachment.crossCycleLength,
        p13PositionDistance_eq_sub_of_lt less, gapEq] using power
    · intro rightPos rightMem leftPos leftMem less gapEq
      apply compatible leftPos rightPos (by simpa using leftMem)
        (by simpa using rightMem)
      have distanceSymm :
          Graph.InducedPathAttachment.positionDistance leftPos rightPos =
            Graph.InducedPathAttachment.positionDistance rightPos leftPos := by
        simp [Graph.InducedPathAttachment.positionDistance,
          Nat.max_comm, Nat.min_comm]
      simpa [Graph.InducedPathAttachment.crossCycleLength, distanceSymm,
        p13PositionDistance_eq_sub_of_lt less, gapEq] using power

end Erdos64EG.Internal
