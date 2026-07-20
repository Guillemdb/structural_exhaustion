import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAudit03

namespace Erdos64EG.Internal

set_option maxRecDepth 100000

theorem p13RowsOne_codeAudit_80 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 80 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 80 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_80 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 80 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 80 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_81 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 81 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 81 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_81 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 81 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 81 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_82 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 82 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 82 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_82 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 82 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 82 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_83 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 83 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 83 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_83 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 83 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 83 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_84 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 84 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 84 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_84 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 84 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 84 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_85 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 85 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 85 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_85 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 85 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 85 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_86 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 86 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 86 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_86 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 86 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 86 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_87 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 87 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 87 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_87 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 87 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 87 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_88 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 88 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 88 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_88 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 88 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 88 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_89 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 89 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 89 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_89 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 89 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 89 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_90 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 90 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 90 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_90 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 90 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 90 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_91 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 91 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 91 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_91 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 91 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 91 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_92 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 92 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 92 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_92 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 92 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 92 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_93 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 93 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 93 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_93 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 93 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 93 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_94 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 94 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 94 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_94 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 94 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 94 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_95 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 95 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 95 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_95 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 95 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 95 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_96 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 96 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 96 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_96 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 96 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 96 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_97 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 97 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 97 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_97 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 97 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 97 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_98 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 98 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 98 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_98 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 98 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 98 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_99 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 99 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 99 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_99 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 99 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 99 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

end Erdos64EG.Internal

