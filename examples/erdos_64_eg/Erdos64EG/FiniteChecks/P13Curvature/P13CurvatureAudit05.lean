import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAudit04

namespace Erdos64EG.Internal

set_option maxRecDepth 100000

theorem p13RowsOne_codeAudit_100 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 100 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 100 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_100 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 100 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 100 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_101 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 101 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 101 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_101 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 101 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 101 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_102 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 102 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 102 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_102 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 102 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 102 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_103 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 103 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 103 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_103 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 103 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 103 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_104 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 104 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 104 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_104 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 104 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 104 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_105 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 105 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 105 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_105 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 105 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 105 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_106 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 106 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 106 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_106 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 106 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 106 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_107 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 107 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 107 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_107 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 107 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 107 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_108 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 108 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 108 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_108 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 108 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 108 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_109 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 109 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 109 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_109 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 109 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 109 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_110 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 110 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 110 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_110 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 110 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 110 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_111 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 111 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 111 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_111 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 111 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 111 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_112 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 112 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 112 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_112 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 112 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 112 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_113 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 113 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 113 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_113 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 113 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 113 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_114 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 114 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 114 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_114 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 114 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 114 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_115 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 115 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 115 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_115 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 115 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 115 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_116 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 116 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 116 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_116 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 116 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 116 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_117 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 117 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 117 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_117 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 117 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 117 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_118 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 118 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 118 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_118 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 118 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 118 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_119 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 119 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 119 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_119 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 119 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 119 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

end Erdos64EG.Internal

