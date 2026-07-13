import Erdos64EG.P13LabelKernel

namespace Erdos64EG.Internal.P13LabelCertificate

open StructuralExhaustion
open P13LabelKernel

/-!
# Cached certificate for the fixed `P₁₃` label table

All finite reflection for the 8192 thirteen-bit codes is confined to this
module.  Lake stores the resulting theorems in this module's `.olean`; later
proof-stage edits consume those cached facts without rerunning the finite
checks.
-/

/-- On thirteen positions, a power-of-two attachment cycle has gap two or
six. -/
theorem pairCycleLength_powerOfTwo_iff_gap_two_or_six
    (left right : Fin 13) (left_lt_right : left < right) :
    PowerOfTwoLength
        (Graph.InducedPathAttachment.pairCycleLength left right) ↔
      right.1 - left.1 = 2 ∨ right.1 - left.1 = 6 := by
  native_decide +revert

/-- Population count agrees with the decoded finite-set cardinality. -/
theorem labelCode_card (code : Code) :
    (Graph.InducedPathAttachment.labelCodeEquiv 13 code).card =
      code.cpop.toNat := by
  letI : FinEnum Code := codes
  native_decide +revert

/-- One cached computation certifies the table cardinality and all seven size
fibres. -/
theorem table_computation :
    classification.classCount = 399 ∧
      (labelsOfSize 1 = 13 ∧
       labelsOfSize 2 = 60 ∧
       labelsOfSize 3 = 122 ∧
       labelsOfSize 4 = 122 ∧
       labelsOfSize 5 = 63 ∧
       labelsOfSize 6 = 17 ∧
       labelsOfSize 7 = 2) := by
  native_decide

/-- Every accepted code is nonempty and has at most seven selected
positions. -/
theorem legalCode_card_bounds_computation :
    ∀ code : Code, codeLegalBool code = true →
      1 ≤ code.cpop.toNat ∧ code.cpop.toNat ≤ 7 := by
  letI : FinEnum Code := codes
  native_decide

/-- The fixed source universe contains exactly `2¹³` candidates. -/
theorem candidate_count : classification.candidateCount = 8192 := by
  native_decide

end Erdos64EG.Internal.P13LabelCertificate
