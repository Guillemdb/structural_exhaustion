import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureBitSemantic

namespace Erdos64EG.Internal

set_option maxRecDepth 100000

theorem p13RowsOne_codeAudit_0 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 0 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 0 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_0 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 0 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 0 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_1 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 1 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_1 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 1 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_2 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 2 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 2 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_2 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 2 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 2 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_3 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 3 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 3 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_3 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 3 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 3 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_4 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 4 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 4 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_4 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 4 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 4 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_5 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 5 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 5 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_5 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 5 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 5 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_6 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 6 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 6 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_6 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 6 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 6 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_7 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 7 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 7 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_7 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 7 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 7 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_8 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 8 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 8 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_8 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 8 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 8 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_9 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 9 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 9 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_9 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 9 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 9 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_10 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 10 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 10 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_10 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 10 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 10 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_11 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 11 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 11 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_11 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 11 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 11 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_12 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 12 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 12 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_12 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 12 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 12 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_13 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 13 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 13 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_13 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 13 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 13 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_14 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 14 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 14 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_14 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 14 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 14 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_15 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 15 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 15 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_15 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 15 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 15 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_16 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 16 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 16 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_16 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 16 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 16 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_17 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 17 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 17 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_17 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 17 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 17 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_18 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 18 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 18 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_18 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 18 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 18 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_19 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 19 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 19 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_19 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 19 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 19 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

end Erdos64EG.Internal
