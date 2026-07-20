import Erdos64EG.FiniteChecks.P13Labels.P13LabelKernel
import StructuralExhaustion.Core.FiniteWeightedAutomaton
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Vector.Basic

namespace Erdos64EG.Internal.P13ParityLabelCount

open StructuralExhaustion

/-!
# Symbolic parity decomposition of the P13 label carrier

The forbidden gaps `2` and `6` preserve parity.  This file begins the exact
carrier equivalence used to reduce node [18]'s count to the two bounded-word
counts on seven even and six odd positions.  No label universe is enumerated.
-/

/-- Interleave seven even and six odd coordinates into thirteen positions. -/
def parityPosition : Fin 7 ⊕ Fin 6 → Fin 13
  | .inl position => ⟨2 * position.1, by omega⟩
  | .inr position => ⟨2 * position.1 + 1, by omega⟩

theorem parityPosition_bijective : Function.Bijective parityPosition := by
  constructor
  · intro left right equal
    cases left with
    | inl left =>
        cases right with
        | inl right =>
            apply congrArg Sum.inl
            apply Fin.ext
            have valueEqual : 2 * left.1 = 2 * right.1 :=
              congrArg Fin.val equal
            omega
        | inr right =>
            have valueEqual : 2 * left.1 = 2 * right.1 + 1 :=
              congrArg Fin.val equal
            omega
    | inr left =>
        cases right with
        | inl right =>
            have valueEqual : 2 * left.1 + 1 = 2 * right.1 :=
              congrArg Fin.val equal
            omega
        | inr right =>
            apply congrArg Sum.inr
            apply Fin.ext
            have valueEqual : 2 * left.1 + 1 = 2 * right.1 + 1 :=
              congrArg Fin.val equal
            omega
  · intro position
    by_cases even : Even position.1
    · rcases even with ⟨half, halfEq⟩
      have halfLt : half < 7 := by omega
      refine ⟨Sum.inl ⟨half, halfLt⟩, ?_⟩
      apply Fin.ext
      simp [parityPosition]
      omega
    · have odd : Odd position.1 := Nat.not_even_iff_odd.mp even
      rcases odd with ⟨half, halfEq⟩
      have halfLt : half < 6 := by omega
      refine ⟨Sum.inr ⟨half, halfLt⟩, ?_⟩
      apply Fin.ext
      simp [parityPosition]
      omega

/-- Exact position equivalence underlying the parity split. -/
noncomputable def parityPositionEquiv : Fin 7 ⊕ Fin 6 ≃ Fin 13 :=
  Equiv.ofBijective parityPosition parityPosition_bijective

/-- A thirteen-position support is exactly a pair of supports on its even
and odd coordinates. -/
noncomputable def parityLabelEquiv :
    Finset (Fin 7) × Finset (Fin 6) ≃ Finset (Fin 13) :=
  Finset.sumEquiv.symm.toEquiv.trans (Equiv.finsetCongr parityPositionEquiv)

theorem parityLabelEquiv_card (labels : Finset (Fin 7) × Finset (Fin 6)) :
    (parityLabelEquiv labels).card = labels.1.card + labels.2.card := by
  simp [parityLabelEquiv]

@[simp] theorem even_mem_parityLabelEquiv
    (labels : Finset (Fin 7) × Finset (Fin 6)) (position : Fin 7) :
    parityPosition (.inl position) ∈ parityLabelEquiv labels ↔
      position ∈ labels.1 := by
  simp [parityLabelEquiv, parityPositionEquiv]

@[simp] theorem odd_mem_parityLabelEquiv
    (labels : Finset (Fin 7) × Finset (Fin 6)) (position : Fin 6) :
    parityPosition (.inr position) ∈ parityLabelEquiv labels ↔
      position ∈ labels.2 := by
  simp [parityLabelEquiv, parityPositionEquiv]

/-- The scaled half-word constraint: no two selected coordinates differ by
one or three. -/
def HalfGapSafe {length : Nat} (label : Finset (Fin length)) : Prop :=
  ∀ left ∈ label, ∀ right ∈ label, left < right →
    right.1 - left.1 ≠ 1 ∧ right.1 - left.1 ≠ 3

/-- Characteristic functions identify finite coordinate supports with Boolean
words, without constructing a powerset table. -/
noncomputable def finsetBoolEquiv (length : Nat) :
    Finset (Fin length) ≃ (Fin length → Bool) where
  toFun label position := decide (position ∈ label)
  invFun word := Finset.univ.filter fun position => word position = true
  left_inv label := by
    ext position
    simp
  right_inv word := by
    funext position
    cases value : word position <;> simp [value]

/-- Characteristic-list form of a finite coordinate support. -/
noncomputable def characteristicWord {length : Nat}
    (label : Finset (Fin length)) : List.Vector Bool length :=
  (Equiv.vectorEquivFin Bool length).symm (finsetBoolEquiv length label)

/-- The characteristic-word construction is an exact equivalence. -/
noncomputable def characteristicWordEquiv (length : Nat) :
    Finset (Fin length) ≃ List.Vector Bool length :=
  (finsetBoolEquiv length).trans (Equiv.vectorEquivFin Bool length).symm

@[simp] theorem characteristicWord_get {length : Nat}
    (label : Finset (Fin length)) (position : Fin length) :
    (characteristicWord label).get position = decide (position ∈ label) := by
  exact List.Vector.get_ofFn _ _

/-- Gap avoidance at distances two and six is exactly the product of the
two parity-local distance-one/three constraints. -/
theorem parityLabelEquiv_gapSafe
    (labels : Finset (Fin 7) × Finset (Fin 6)) :
    (∀ left ∈ parityLabelEquiv labels,
      ∀ right ∈ parityLabelEquiv labels, left < right →
        right.1 - left.1 ≠ 2 ∧ right.1 - left.1 ≠ 6) ↔
      HalfGapSafe labels.1 ∧ HalfGapSafe labels.2 := by
  constructor
  · intro safe
    constructor
    · intro left leftMem right rightMem leftLt
      have mappedLeftMem :
          parityPosition (.inl left) ∈ parityLabelEquiv labels :=
        (even_mem_parityLabelEquiv labels left).2 leftMem
      have mappedRightMem :
          parityPosition (.inl right) ∈ parityLabelEquiv labels :=
        (even_mem_parityLabelEquiv labels right).2 rightMem
      have mappedLt :
          parityPosition (.inl left) < parityPosition (.inl right) := by
        simp [parityPosition]
        omega
      have result := safe _ mappedLeftMem _ mappedRightMem mappedLt
      simp [parityPosition] at result
      omega
    · intro left leftMem right rightMem leftLt
      have mappedLeftMem :
          parityPosition (.inr left) ∈ parityLabelEquiv labels :=
        (odd_mem_parityLabelEquiv labels left).2 leftMem
      have mappedRightMem :
          parityPosition (.inr right) ∈ parityLabelEquiv labels :=
        (odd_mem_parityLabelEquiv labels right).2 rightMem
      have mappedLt :
          parityPosition (.inr left) < parityPosition (.inr right) := by
        simp [parityPosition]
        omega
      have result := safe _ mappedLeftMem _ mappedRightMem mappedLt
      simp [parityPosition] at result
      omega
  · rintro ⟨evenSafe, oddSafe⟩ left leftMem right rightMem leftLt
    generalize leftDef : parityPositionEquiv.symm left = leftPreimage
    generalize rightDef : parityPositionEquiv.symm right = rightPreimage
    have leftEq : parityPosition leftPreimage = left := by
      rw [← leftDef]
      exact parityPositionEquiv.apply_symm_apply left
    have rightEq : parityPosition rightPreimage = right := by
      rw [← rightDef]
      exact parityPositionEquiv.apply_symm_apply right
    cases leftPreimage with
    | inl leftHalf =>
        change parityPosition (.inl leftHalf) = left at leftEq
        cases rightPreimage with
        | inl rightHalf =>
            change parityPosition (.inl rightHalf) = right at rightEq
            have leftValueEq := congrArg Fin.val leftEq
            have rightValueEq := congrArg Fin.val rightEq
            have leftHalfMem : leftHalf ∈ labels.1 := by
              apply (even_mem_parityLabelEquiv labels leftHalf).1
              rw [leftEq]
              exact leftMem
            have rightHalfMem : rightHalf ∈ labels.1 := by
              apply (even_mem_parityLabelEquiv labels rightHalf).1
              rw [rightEq]
              exact rightMem
            have halfLt : leftHalf < rightHalf := by
              simp [parityPosition] at leftValueEq rightValueEq
              omega
            have result := evenSafe leftHalf leftHalfMem rightHalf
              rightHalfMem halfLt
            simp [parityPosition] at leftValueEq rightValueEq
            omega

        | inr rightHalf =>
            change parityPosition (.inr rightHalf) = right at rightEq
            have leftValueEq := congrArg Fin.val leftEq
            have rightValueEq := congrArg Fin.val rightEq
            simp [parityPosition] at leftValueEq rightValueEq
            omega
    | inr leftHalf =>
        change parityPosition (.inr leftHalf) = left at leftEq
        cases rightPreimage with
        | inl rightHalf =>
            change parityPosition (.inl rightHalf) = right at rightEq
            have leftValueEq := congrArg Fin.val leftEq
            have rightValueEq := congrArg Fin.val rightEq
            simp [parityPosition] at leftValueEq rightValueEq
            omega
        | inr rightHalf =>
            change parityPosition (.inr rightHalf) = right at rightEq
            have leftValueEq := congrArg Fin.val leftEq
            have rightValueEq := congrArg Fin.val rightEq
            have leftHalfMem : leftHalf ∈ labels.2 := by
              apply (odd_mem_parityLabelEquiv labels leftHalf).1
              rw [leftEq]
              exact leftMem
            have rightHalfMem : rightHalf ∈ labels.2 := by
              apply (odd_mem_parityLabelEquiv labels rightHalf).1
              rw [rightEq]
              exact rightMem
            have halfLt : leftHalf < rightHalf := by
              simp [parityPosition] at leftValueEq rightValueEq
              omega
            have result := oddSafe leftHalf leftHalfMem rightHalf
              rightHalfMem halfLt
            simp [parityPosition] at leftValueEq rightValueEq
            omega

theorem parityLabelEquiv_nonempty
    (labels : Finset (Fin 7) × Finset (Fin 6)) :
    (parityLabelEquiv labels).Nonempty ↔
      labels.1.Nonempty ∨ labels.2.Nonempty := by
  constructor
  · rintro ⟨position, positionMem⟩
    generalize preimageDef : parityPositionEquiv.symm position = preimage
    have positionEq : parityPosition preimage = position := by
      rw [← preimageDef]
      exact parityPositionEquiv.apply_symm_apply position
    cases preimage with
    | inl half =>
        left
        refine ⟨half, ?_⟩
        apply (even_mem_parityLabelEquiv labels half).1
        rw [positionEq]
        exact positionMem
    | inr half =>
        right
        refine ⟨half, ?_⟩
        apply (odd_mem_parityLabelEquiv labels half).1
        rw [positionEq]
        exact positionMem
  · rintro (leftNonempty | rightNonempty)
    · rcases leftNonempty with ⟨position, positionMem⟩
      exact ⟨parityPosition (.inl position),
        (even_mem_parityLabelEquiv labels position).2 positionMem⟩
    · rcases rightNonempty with ⟨position, positionMem⟩
      exact ⟨parityPosition (.inr position),
        (odd_mem_parityLabelEquiv labels position).2 positionMem⟩

theorem parityLabelEquiv_legal
    (labels : Finset (Fin 7) × Finset (Fin 6)) :
    ((parityLabelEquiv labels).Nonempty ∧
      ∀ left ∈ parityLabelEquiv labels,
        ∀ right ∈ parityLabelEquiv labels, left < right →
          right.1 - left.1 ≠ 2 ∧ right.1 - left.1 ≠ 6) ↔
      (labels.1.Nonempty ∨ labels.2.Nonempty) ∧
        HalfGapSafe labels.1 ∧ HalfGapSafe labels.2 := by
  rw [parityLabelEquiv_nonempty, parityLabelEquiv_gapSafe]

/-! ## Symbolic half-word recurrence

The automaton remembers only the preceding three bits.  A selected new bit is
rejected exactly when the bit one or three positions behind was selected.
Thus the executable computation has eight states, independently of the label
universe represented by the recurrence.
-/

abbrev HalfGapState := Bool × Bool × Bool

def halfGapMachine :
    Core.FiniteWeightedAutomaton.Machine HalfGapState Bool where
  symbols := Core.Enumeration.bool
  step history selected :=
    if selected && (history.1 || history.2.2) then none
    else some (selected, history.1, history.2.1)
  weight selected := if selected then 1 else 0

def halfGapStart : HalfGapState := (false, false, false)

/-- Structural semantics of the three-bit history machine. -/
def HalfWordSafe : HalfGapState → List Bool → Prop
  | _, [] => True
  | history, selected :: tail =>
      ¬(selected = true ∧ (history.1 = true ∨ history.2.2 = true)) ∧
        HalfWordSafe (selected, history.1, history.2.1) tail

def trueWeight : List Bool → Nat
  | [] => 0
  | selected :: tail => (if selected then 1 else 0) + trueWeight tail

theorem halfGapMachine_accepts_iff
    (history : HalfGapState) (word : List Bool) (total : Nat) :
    halfGapMachine.Accepts history word total ↔
      HalfWordSafe history word ∧ trueWeight word = total := by
  induction word generalizing history total with
  | nil => simp [Core.FiniteWeightedAutomaton.Machine.Accepts,
      HalfWordSafe, trueWeight, eq_comm]
  | cons selected tail ih =>
      constructor
      · rintro ⟨next, transition, fits, accepted⟩
        have admitted :
            ¬(selected = true ∧
              (history.1 = true ∨ history.2.2 = true)) := by
          intro forbidden
          rcases forbidden with ⟨rfl, conflict⟩
          cases conflict with
          | inl conflict => simp [halfGapMachine, conflict] at transition
          | inr conflict => simp [halfGapMachine, conflict] at transition
        have nextEq : next = (selected, history.1, history.2.1) := by
          simpa [halfGapMachine, admitted, Bool.and_eq_true,
            Bool.or_eq_true] using transition.symm
        subst next
        change (if selected then 1 else 0) ≤ total at fits
        have tailResult :=
          (ih (selected, history.1, history.2.1)
            (total - (if selected then 1 else 0))).1 accepted
        refine ⟨⟨admitted, tailResult.1⟩, ?_⟩
        cases selected <;> simp [trueWeight] at fits tailResult ⊢ <;> omega
      · rintro ⟨⟨admitted, tailSafe⟩, weightEq⟩
        refine ⟨(selected, history.1, history.2.1), ?_, ?_, ?_⟩
        · simp [halfGapMachine, admitted, Bool.and_eq_true,
            Bool.or_eq_true]
        · change (if selected then 1 else 0) ≤ total
          cases selected <;> simp [trueWeight] at weightEq ⊢ <;> omega
        · apply (ih (selected, history.1, history.2.1)
              (total - (if selected then 1 else 0))).2
          refine ⟨tailSafe, ?_⟩
          cases selected <;> simp [halfGapMachine, trueWeight] at weightEq ⊢ <;> omega

theorem characteristicWord_six_toList (label : Finset (Fin 6)) :
    (characteristicWord label).toList =
      [decide ((0 : Fin 6) ∈ label), decide ((1 : Fin 6) ∈ label),
       decide ((2 : Fin 6) ∈ label), decide ((3 : Fin 6) ∈ label),
       decide ((4 : Fin 6) ∈ label), decide ((5 : Fin 6) ∈ label)] := by
  have vectorEq : characteristicWord label =
      ⟨[decide ((0 : Fin 6) ∈ label), decide ((1 : Fin 6) ∈ label),
        decide ((2 : Fin 6) ∈ label), decide ((3 : Fin 6) ∈ label),
        decide ((4 : Fin 6) ∈ label), decide ((5 : Fin 6) ∈ label)], by simp⟩ := by
    ext position
    have value := characteristicWord_get label position
    fin_cases position <;> exact value
  exact congrArg Subtype.val vectorEq

theorem characteristicWord_seven_toList (label : Finset (Fin 7)) :
    (characteristicWord label).toList =
      [decide ((0 : Fin 7) ∈ label), decide ((1 : Fin 7) ∈ label),
       decide ((2 : Fin 7) ∈ label), decide ((3 : Fin 7) ∈ label),
       decide ((4 : Fin 7) ∈ label), decide ((5 : Fin 7) ∈ label),
       decide ((6 : Fin 7) ∈ label)] := by
  have vectorEq : characteristicWord label =
      ⟨[decide ((0 : Fin 7) ∈ label), decide ((1 : Fin 7) ∈ label),
        decide ((2 : Fin 7) ∈ label), decide ((3 : Fin 7) ∈ label),
        decide ((4 : Fin 7) ∈ label), decide ((5 : Fin 7) ∈ label),
        decide ((6 : Fin 7) ∈ label)], by simp⟩ := by
    ext position
    have value := characteristicWord_get label position
    fin_cases position <;> exact value
  exact congrArg Subtype.val vectorEq

theorem halfWordSafe_six_iff (label : Finset (Fin 6)) :
    HalfWordSafe halfGapStart (characteristicWord label).toList ↔
      HalfGapSafe label := by
  rw [characteristicWord_six_toList]
  constructor
  · intro wordSafe left leftMem right rightMem leftLt
    fin_cases left <;> fin_cases right <;>
      simp_all [HalfWordSafe, halfGapStart] <;> omega
  · intro gapSafe
    have h01 : (0 : Fin 6) ∈ label → (1 : Fin 6) ∈ label → False := by
      intro h0 h1; exact (gapSafe 0 h0 1 h1 (by decide)).1 (by decide)
    have h03 : (0 : Fin 6) ∈ label → (3 : Fin 6) ∈ label → False := by
      intro h0 h3; exact (gapSafe 0 h0 3 h3 (by decide)).2 (by decide)
    have h12 : (1 : Fin 6) ∈ label → (2 : Fin 6) ∈ label → False := by
      intro h1 h2; exact (gapSafe 1 h1 2 h2 (by decide)).1 (by decide)
    have h14 : (1 : Fin 6) ∈ label → (4 : Fin 6) ∈ label → False := by
      intro h1 h4; exact (gapSafe 1 h1 4 h4 (by decide)).2 (by decide)
    have h23 : (2 : Fin 6) ∈ label → (3 : Fin 6) ∈ label → False := by
      intro h2 h3; exact (gapSafe 2 h2 3 h3 (by decide)).1 (by decide)
    have h25 : (2 : Fin 6) ∈ label → (5 : Fin 6) ∈ label → False := by
      intro h2 h5; exact (gapSafe 2 h2 5 h5 (by decide)).2 (by decide)
    have h34 : (3 : Fin 6) ∈ label → (4 : Fin 6) ∈ label → False := by
      intro h3 h4; exact (gapSafe 3 h3 4 h4 (by decide)).1 (by decide)
    have h45 : (4 : Fin 6) ∈ label → (5 : Fin 6) ∈ label → False := by
      intro h4 h5; exact (gapSafe 4 h4 5 h5 (by decide)).1 (by decide)
    simp only [HalfWordSafe, halfGapStart]
    simp only [Bool.false_eq_true, Bool.or_self, or_false, and_false,
      not_false_eq_true, true_and]
    simp only [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · rintro ⟨h1, h0⟩; exact h01 h0 h1
    · rintro ⟨h2, h1⟩; exact h12 h1 h2
    · rintro ⟨h3, h2 | h0⟩
      · exact h23 h2 h3
      · exact h03 h0 h3
    · rintro ⟨h4, h3 | h1⟩
      · exact h34 h3 h4
      · exact h14 h1 h4
    · rintro ⟨h5, h4 | h2⟩
      · exact h45 h4 h5
      · exact h25 h2 h5

theorem halfWordSafe_seven_iff (label : Finset (Fin 7)) :
    HalfWordSafe halfGapStart (characteristicWord label).toList ↔
      HalfGapSafe label := by
  rw [characteristicWord_seven_toList]
  constructor
  · intro wordSafe left leftMem right rightMem leftLt
    fin_cases left <;> fin_cases right <;>
      simp_all [HalfWordSafe, halfGapStart] <;> omega
  · intro gapSafe
    have h01 : (0 : Fin 7) ∈ label → (1 : Fin 7) ∈ label → False := by
      intro h0 h1; exact (gapSafe 0 h0 1 h1 (by decide)).1 (by decide)
    have h03 : (0 : Fin 7) ∈ label → (3 : Fin 7) ∈ label → False := by
      intro h0 h3; exact (gapSafe 0 h0 3 h3 (by decide)).2 (by decide)
    have h12 : (1 : Fin 7) ∈ label → (2 : Fin 7) ∈ label → False := by
      intro h1 h2; exact (gapSafe 1 h1 2 h2 (by decide)).1 (by decide)
    have h14 : (1 : Fin 7) ∈ label → (4 : Fin 7) ∈ label → False := by
      intro h1 h4; exact (gapSafe 1 h1 4 h4 (by decide)).2 (by decide)
    have h23 : (2 : Fin 7) ∈ label → (3 : Fin 7) ∈ label → False := by
      intro h2 h3; exact (gapSafe 2 h2 3 h3 (by decide)).1 (by decide)
    have h25 : (2 : Fin 7) ∈ label → (5 : Fin 7) ∈ label → False := by
      intro h2 h5; exact (gapSafe 2 h2 5 h5 (by decide)).2 (by decide)
    have h34 : (3 : Fin 7) ∈ label → (4 : Fin 7) ∈ label → False := by
      intro h3 h4; exact (gapSafe 3 h3 4 h4 (by decide)).1 (by decide)
    have h36 : (3 : Fin 7) ∈ label → (6 : Fin 7) ∈ label → False := by
      intro h3 h6; exact (gapSafe 3 h3 6 h6 (by decide)).2 (by decide)
    have h45 : (4 : Fin 7) ∈ label → (5 : Fin 7) ∈ label → False := by
      intro h4 h5; exact (gapSafe 4 h4 5 h5 (by decide)).1 (by decide)
    have h56 : (5 : Fin 7) ∈ label → (6 : Fin 7) ∈ label → False := by
      intro h5 h6; exact (gapSafe 5 h5 6 h6 (by decide)).1 (by decide)
    simp only [HalfWordSafe, halfGapStart]
    simp only [Bool.false_eq_true, Bool.or_self, or_false, and_false,
      not_false_eq_true, true_and]
    simp only [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rintro ⟨h1, h0⟩; exact h01 h0 h1
    · rintro ⟨h2, h1⟩; exact h12 h1 h2
    · rintro ⟨h3, h2 | h0⟩
      · exact h23 h2 h3
      · exact h03 h0 h3
    · rintro ⟨h4, h3 | h1⟩
      · exact h34 h3 h4
      · exact h14 h1 h4
    · rintro ⟨h5, h4 | h2⟩
      · exact h45 h4 h5
      · exact h25 h2 h5
    · rintro ⟨h6, h5 | h3⟩
      · exact h56 h5 h6
      · exact h36 h3 h6

theorem trueWeight_characteristic_six (label : Finset (Fin 6)) :
    trueWeight (characteristicWord label).toList = label.card := by
  rw [characteristicWord_six_toList]
  classical
  have countSelected :
      (∑ position : Fin 6, if position ∈ label then 1 else 0) =
        label.card := by
    rw [← Finset.sum_filter]
    have filtered : (Finset.univ.filter fun position : Fin 6 =>
        position ∈ label) = label := by ext; simp
    rw [filtered, ← Finset.card_eq_sum_ones]
  simp only [trueWeight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] at countSelected
  simp only [decide_eq_true_eq]
  norm_num at countSelected ⊢
  exact countSelected

theorem trueWeight_characteristic_seven (label : Finset (Fin 7)) :
    trueWeight (characteristicWord label).toList = label.card := by
  rw [characteristicWord_seven_toList]
  classical
  have countSelected :
      (∑ position : Fin 7, if position ∈ label then 1 else 0) =
        label.card := by
    rw [← Finset.sum_filter]
    have filtered : (Finset.univ.filter fun position : Fin 7 =>
        position ∈ label) = label := by ext; simp
    rw [filtered, ← Finset.card_eq_sum_ones]
  simp only [trueWeight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] at countSelected
  simp only [decide_eq_true_eq]
  norm_num at countSelected ⊢
  exact countSelected

/-- A parity-local safe support with a prescribed number of selected
coordinates. -/
abbrev HalfSafeSized (length weight : Nat) :=
  {label : Finset (Fin length) //
    HalfGapSafe label ∧ label.card = weight}

@[implicit_reducible]
noncomputable def halfSafeSizedEnum (length weight : Nat) :
    FinEnum (HalfSafeSized length weight) := by
  classical
  infer_instance

/-- Restrict the characteristic-word equivalence to the language recognized
by the symbolic half-gap automaton. -/
noncomputable def halfSafeSizedEquivAccepted
    (length weight : Nat)
    (safe_iff : ∀ label : Finset (Fin length),
      HalfWordSafe halfGapStart (characteristicWord label).toList ↔
        HalfGapSafe label)
    (weight_eq : ∀ label : Finset (Fin length),
      trueWeight (characteristicWord label).toList = label.card) :
    HalfSafeSized length weight ≃
      {word // word ∈ halfGapMachine.words length halfGapStart weight} :=
  Equiv.ofBijective
    (fun label => ⟨(characteristicWord label.1).toList,
      (halfGapMachine.mem_words_iff length halfGapStart weight _).2
        ⟨(characteristicWord label.1).property,
          (halfGapMachine_accepts_iff halfGapStart _ weight).2
            ⟨(safe_iff label.1).2 label.2.1,
              (weight_eq label.1).trans label.2.2⟩⟩⟩)
    (by
      constructor
      · intro left right equal
        have listEqual :
            (characteristicWord left.1).toList =
              (characteristicWord right.1).toList :=
          congrArg (fun accepted => accepted.1) equal
        apply Subtype.ext
        apply (characteristicWordEquiv length).injective
        apply Subtype.ext
        exact listEqual
      · intro accepted
        have acceptedFacts :=
          (halfGapMachine.mem_words_iff length halfGapStart weight
            accepted.1).1 accepted.2
        let vector : List.Vector Bool length :=
          ⟨accepted.1, acceptedFacts.1⟩
        let label : Finset (Fin length) :=
          (characteristicWordEquiv length).symm vector
        have characteristicEq : characteristicWord label = vector := by
          exact (characteristicWordEquiv length).apply_symm_apply vector
        have wordEq : (characteristicWord label).toList = accepted.1 :=
          congrArg Subtype.val characteristicEq
        have semantic :=
          (halfGapMachine_accepts_iff halfGapStart accepted.1 weight).1
            acceptedFacts.2
        have labelSafe : HalfGapSafe label := by
          apply (safe_iff label).1
          rw [wordEq]
          exact semantic.1
        have labelWeight : label.card = weight := by
          rw [← weight_eq label, wordEq]
          exact semantic.2
        refine ⟨⟨label, labelSafe, labelWeight⟩, ?_⟩
        apply Subtype.ext
        exact wordEq)

theorem halfSafeSized_card_eq_count_six (weight : Nat) :
    (halfSafeSizedEnum 6 weight).card =
      halfGapMachine.count 6 halfGapStart weight := by
  apply halfGapMachine.carrier_card_eq_count_of_equiv
  exact halfSafeSizedEquivAccepted 6 weight halfWordSafe_six_iff
    trueWeight_characteristic_six

theorem halfSafeSized_card_eq_count_seven (weight : Nat) :
    (halfSafeSizedEnum 7 weight).card =
      halfGapMachine.count 7 halfGapStart weight := by
  apply halfGapMachine.carrier_card_eq_count_of_equiv
  exact halfSafeSizedEquivAccepted 7 weight halfWordSafe_seven_iff
    trueWeight_characteristic_seven

/-- Pair of parity-local safe supports with prescribed total size. -/
abbrev ParitySafeSized (weight : Nat) :=
  {labels : Finset (Fin 7) × Finset (Fin 6) //
    HalfGapSafe labels.1 ∧ HalfGapSafe labels.2 ∧
      labels.1.card + labels.2.card = weight}

private theorem right_eq_sub_of_add_eq {left right total : Nat}
    (equal : left + right = total) : right = total - left := by
  omega

/-- Split a fixed total size at the even-support contribution. -/
noncomputable def paritySafeSizedEquivSigma (weight : Nat) :
    ParitySafeSized weight ≃
      Σ evenWeight : Fin (weight + 1),
        HalfSafeSized 7 evenWeight.1 ×
          HalfSafeSized 6 (weight - evenWeight.1) :=
  Equiv.ofBijective
    (fun labels =>
      ⟨⟨labels.1.1.card, by omega⟩,
        ⟨⟨labels.1.1, ⟨labels.2.1, rfl⟩⟩,
          ⟨labels.1.2, ⟨labels.2.2.1,
            right_eq_sub_of_add_eq labels.2.2.2⟩⟩⟩⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        have pairEqual := congrArg (fun value =>
          (value.2.1.1, value.2.2.1)) equal
        exact pairEqual
      · rintro ⟨⟨evenWeight, evenWeightBound⟩,
          ⟨⟨evenLabel, evenSafe, evenCard⟩,
            ⟨oddLabel, oddSafe, oddCard⟩⟩⟩
        change evenLabel.card = evenWeight at evenCard
        change oddLabel.card = weight - evenWeight at oddCard
        subst evenWeight
        have total : evenLabel.card + oddLabel.card = weight := by
          rw [oddCard]
          omega
        refine ⟨⟨(evenLabel, oddLabel), evenSafe, oddSafe, total⟩, ?_⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Prod.ext <;> apply Subtype.ext <;> rfl)

/-- Thirteen-position supports avoiding gaps two and six, graded by size. -/
abbrev GapSafeSized13 (weight : Nat) :=
  {label : Finset (Fin 13) //
    (∀ left ∈ label, ∀ right ∈ label, left < right →
      right.1 - left.1 ≠ 2 ∧ right.1 - left.1 ≠ 6) ∧
    label.card = weight}

noncomputable def gapSafeSized13EquivParity (weight : Nat) :
    GapSafeSized13 weight ≃ ParitySafeSized weight :=
  Equiv.ofBijective
    (fun label =>
      let labels := parityLabelEquiv.symm label.1
      ⟨labels,
        (parityLabelEquiv_gapSafe labels).1 (by
          simpa [labels] using label.2.1) |>.1,
        (parityLabelEquiv_gapSafe labels).1 (by
          simpa [labels] using label.2.1) |>.2,
        by
          rw [← parityLabelEquiv_card labels]
          simpa [labels] using label.2.2⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        apply parityLabelEquiv.symm.injective
        exact congrArg Subtype.val equal
      · intro labels
        refine ⟨⟨parityLabelEquiv labels.1, ?_, ?_⟩, ?_⟩
        · exact (parityLabelEquiv_gapSafe labels.1).2
            ⟨labels.2.1, labels.2.2.1⟩
        · rw [parityLabelEquiv_card]
          exact labels.2.2.2
        · apply Subtype.ext
          exact parityLabelEquiv.symm_apply_apply labels.1)

private theorem halfSafeSized_natCard_six (weight : Nat) :
    Nat.card (HalfSafeSized 6 weight) =
      halfGapMachine.count 6 halfGapStart weight := by
  letI : FinEnum (HalfSafeSized 6 weight) := halfSafeSizedEnum 6 weight
  rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard]
  exact halfSafeSized_card_eq_count_six weight

private theorem halfSafeSized_natCard_seven (weight : Nat) :
    Nat.card (HalfSafeSized 7 weight) =
      halfGapMachine.count 7 halfGapStart weight := by
  letI : FinEnum (HalfSafeSized 7 weight) := halfSafeSizedEnum 7 weight
  rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard]
  exact halfSafeSized_card_eq_count_seven weight

private theorem listRange_map_sum_eq_finset_sum (f : Nat → Nat) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append,
        listRange_map_sum_eq_finset_sum f n, Finset.sum_range_succ]
      simp

/-- Each legal size fibre is counted by convolving the two parity-local
automata.  The proof transports cardinalities through the explicit graded
equivalences and never enumerates the ambient thirteen-bit universe. -/
theorem gapSafeSized13_natCard_eq_convolution (weight : Nat) :
    Nat.card (GapSafeSized13 weight) =
      Core.FiniteWeightedAutomaton.convolution
        (halfGapMachine.count 7 halfGapStart)
        (halfGapMachine.count 6 halfGapStart) weight := by
  rw [Nat.card_congr (gapSafeSized13EquivParity weight)]
  rw [Nat.card_congr (paritySafeSizedEquivSigma weight)]
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod, halfSafeSized_natCard_seven,
    halfSafeSized_natCard_six]
  rw [Core.FiniteWeightedAutomaton.convolution,
    listRange_map_sum_eq_finset_sum]
  exact Fin.sum_univ_eq_sum_range
      (fun leftWeight : Nat =>
        halfGapMachine.count 7 halfGapStart leftWeight *
          halfGapMachine.count 6 halfGapStart (weight - leftWeight))
      (weight + 1)

/-- Exact graded enumeration assembled from the two accepted-word carriers. -/
@[implicit_reducible] noncomputable def paritySafeSizedEnum (weight : Nat) :
    FinEnum (ParitySafeSized weight) := by
  let sigmaEnum : FinEnum
      (Σ evenWeight : Fin (weight + 1),
        HalfSafeSized 7 evenWeight.1 ×
          HalfSafeSized 6 (weight - evenWeight.1)) :=
    Core.Enumeration.sigma (inferInstance : FinEnum (Fin (weight + 1)))
      (fun evenWeight => Core.Enumeration.prod
        (halfSafeSizedEnum 7 evenWeight.1)
        (halfSafeSizedEnum 6 (weight - evenWeight.1)))
  letI := sigmaEnum
  exact FinEnum.ofEquiv _ (paritySafeSizedEquivSigma weight)

@[implicit_reducible] noncomputable def gapSafeSized13Enum (weight : Nat) :
    FinEnum (GapSafeSized13 weight) := by
  letI : FinEnum (ParitySafeSized weight) := paritySafeSizedEnum weight
  exact FinEnum.ofEquiv _ (gapSafeSized13EquivParity weight)

private theorem halfGapSafe_card_le_seven
    (label : Finset (Fin 7)) (safe : HalfGapSafe label) :
    label.card ≤ 4 := by
  by_contra tooLarge
  have upper : label.card ≤ 7 := by
    simpa using Finset.card_le_univ label
  have zero : Nat.card (HalfSafeSized 7 label.card) = 0 := by
    rw [halfSafeSized_natCard_seven]
    interval_cases label.card <;> decide
  have inhabited : Nonempty (HalfSafeSized 7 label.card) :=
    ⟨⟨label, safe, rfl⟩⟩
  exact (Nat.card_pos_iff.mpr ⟨inhabited, inferInstance⟩).ne' zero

private theorem halfGapSafe_card_le_six
    (label : Finset (Fin 6)) (safe : HalfGapSafe label) :
    label.card ≤ 3 := by
  by_contra tooLarge
  have upper : label.card ≤ 6 := by
    simpa using Finset.card_le_univ label
  have zero : Nat.card (HalfSafeSized 6 label.card) = 0 := by
    rw [halfSafeSized_natCard_six]
    interval_cases label.card <;> decide
  have inhabited : Nonempty (HalfSafeSized 6 label.card) :=
    ⟨⟨label, safe, rfl⟩⟩
  exact (Nat.card_pos_iff.mpr ⟨inhabited, inferInstance⟩).ne' zero

/-- The graph-level carrier counted at node `[18]`. -/
abbrev GapLegal13 :=
  {label : Finset (Fin 13) //
    label.Nonempty ∧
      ∀ left ∈ label, ∀ right ∈ label, left < right →
        right.1 - left.1 ≠ 2 ∧ right.1 - left.1 ≠ 6}

/-- Partition a legal nonempty label by its (necessarily `1,…,7`) size. -/
noncomputable def gapLegal13EquivSized :
    GapLegal13 ≃ Σ size : Fin 7, GapSafeSized13 (size.1 + 1) :=
  Equiv.ofBijective
    (fun label =>
      let parity := parityLabelEquiv.symm label.1
      have safe := (parityLabelEquiv_gapSafe parity).1 (by
        simpa [parity] using label.2.2)
      have bound : label.1.card ≤ 7 := by
        have cardEqual := parityLabelEquiv_card parity
        rw [parityLabelEquiv.apply_symm_apply label.1] at cardEqual
        exact cardEqual.trans_le (Nat.add_le_add
          (halfGapSafe_card_le_seven parity.1 safe.1)
          (halfGapSafe_card_le_six parity.2 safe.2))
      ⟨⟨label.1.card - 1, by omega⟩,
        ⟨label.1, label.2.2, by
          have positive := Finset.card_pos.mpr label.2.1
          change label.1.card = label.1.card - 1 + 1
          omega⟩⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        exact congrArg (fun value => value.2.1) equal
      · rintro ⟨size, label⟩
        have nonempty : label.1.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro empty
          have := label.2.2
          simp [empty] at this
        refine ⟨⟨label.1, nonempty, label.2.1⟩, ?_⟩
        apply Sigma.ext
        · apply Fin.ext
          simpa [label.2.2]
        · apply (Subtype.heq_iff_coe_eq (fun candidate => by
            constructor <;> intro property
            · exact ⟨property.1, by simpa [label.2.2] using property.2⟩
            · exact ⟨property.1, by simpa [label.2.2] using property.2⟩)).2
          rfl)

/-- Symbolic total: the seven graded fibres contain exactly `399` legal
nonempty labels. -/
theorem gapLegal13_natCard : Nat.card GapLegal13 = 399 := by
  rw [Nat.card_congr gapLegal13EquivSized, Nat.card_sigma]
  simp_rw [gapSafeSized13_natCard_eq_convolution]
  decide

/-- Shallow `399`-row carrier for downstream curvature calculations. -/
@[implicit_reducible] noncomputable def gapLegal13Enum : FinEnum GapLegal13 := by
  let sigmaEnum : FinEnum
      (Σ size : Fin 7, GapSafeSized13 (size.1 + 1)) :=
    Core.Enumeration.sigma (inferInstance : FinEnum (Fin 7))
      (fun size => gapSafeSized13Enum (size.1 + 1))
  letI := sigmaEnum
  exact FinEnum.ofEquiv _ gapLegal13EquivSized

theorem gapLegal13Enum_card : gapLegal13Enum.card = 399 := by
  letI : FinEnum GapLegal13 := gapLegal13Enum
  rw [FinEnum.card_eq_fintypeCard, ← Nat.card_eq_fintype_card]
  exact gapLegal13_natCard

/-- The seven even positions have weight distribution `1,7,11,5,1`. -/
theorem halfGapHistogramSeven :
    halfGapMachine.histogram 7 halfGapStart 7 =
      [1, 7, 11, 5, 1, 0, 0, 0] := by
  decide

/-- The six odd positions have weight distribution `1,6,7,2`. -/
theorem halfGapHistogramSix :
    halfGapMachine.histogram 6 halfGapStart 6 =
      [1, 6, 7, 2, 0, 0, 0] := by
  decide

theorem halfGapTotalSeven :
    ((List.range 8).map (halfGapMachine.count 7 halfGapStart)).sum = 25 := by
  decide

theorem halfGapTotalSix :
    ((List.range 7).map (halfGapMachine.count 6 halfGapStart)).sum = 16 := by
  decide

theorem halfGapConvolution :
    (List.range 14).map
        (Core.FiniteWeightedAutomaton.convolution
          (halfGapMachine.count 7 halfGapStart)
          (halfGapMachine.count 6 halfGapStart)) =
      [1, 13, 60, 122, 122, 63, 17, 2, 0, 0, 0, 0, 0, 0] := by
  decide

theorem halfGapNonemptyTotal : 25 * 16 - 1 = 399 := by
  decide

#print axioms parityPosition_bijective
#print axioms parityLabelEquiv_card
#print axioms halfGapHistogramSeven
#print axioms halfGapHistogramSix
#print axioms halfGapTotalSeven
#print axioms halfGapTotalSix
#print axioms halfGapConvolution

end Erdos64EG.Internal.P13ParityLabelCount
