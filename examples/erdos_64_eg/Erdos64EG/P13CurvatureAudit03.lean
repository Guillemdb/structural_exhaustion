import Erdos64EG.P13CurvatureAudit02

namespace Erdos64EG.Internal

set_option maxRecDepth 100000

theorem p13RowsOne_codeAudit_60 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 60 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 60 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_60 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 60 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 60 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_61 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 61 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 61 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_61 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 61 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 61 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_62 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 62 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 62 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_62 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 62 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 62 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_63 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 63 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 63 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_63 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 63 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 63 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_64 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 64 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 64 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_64 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 64 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 64 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_65 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 65 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 65 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_65 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 65 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 65 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_66 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 66 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 66 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_66 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 66 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 66 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_67 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 67 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 67 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_67 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 67 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 67 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_68 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 68 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 68 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_68 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 68 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 68 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_69 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 69 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 69 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_69 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 69 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 69 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_70 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 70 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 70 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_70 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 70 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 70 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_71 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 71 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 71 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_71 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 71 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 71 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_72 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 72 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 72 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_72 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 72 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 72 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_73 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 73 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 73 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_73 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 73 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 73 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_74 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 74 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 74 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_74 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 74 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 74 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_75 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 75 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 75 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_75 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 75 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 75 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_76 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 76 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 76 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_76 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 76 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 76 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_77 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 77 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 77 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_77 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 77 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 77 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_78 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 78 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 78 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_78 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 78 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 78 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_79 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 79 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 79 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_79 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 79 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 79 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

end Erdos64EG.Internal

