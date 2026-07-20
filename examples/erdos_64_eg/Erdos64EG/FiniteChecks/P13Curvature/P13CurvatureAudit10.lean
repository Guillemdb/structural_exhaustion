import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAudit09

namespace Erdos64EG.Internal

set_option maxRecDepth 100000

theorem p13RowsOne_codeAudit_200 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 200 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 200 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_200 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 200 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 200 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_201 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 201 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 201 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_201 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 201 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 201 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_202 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 202 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 202 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_202 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 202 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 202 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_203 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 203 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 203 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_203 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 203 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 203 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_204 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 204 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 204 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_204 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 204 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 204 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_205 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 205 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 205 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_205 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 205 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 205 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_206 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 206 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 206 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_206 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 206 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 206 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_207 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 207 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 207 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_207 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 207 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 207 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_208 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 208 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 208 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_208 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 208 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 208 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_209 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 209 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 209 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_209 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 209 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 209 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_210 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 210 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 210 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_210 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 210 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 210 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_211 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 211 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 211 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_211 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 211 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 211 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_212 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 212 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 212 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_212 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 212 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 212 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_213 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 213 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 213 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_213 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 213 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 213 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_214 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 214 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 214 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_214 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 214 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 214 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_215 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 215 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 215 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_215 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 215 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 215 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_216 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 216 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 216 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_216 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 216 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 216 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_217 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 217 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 217 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_217 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 217 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 217 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_218 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 218 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 218 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_218 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 218 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 218 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

theorem p13RowsOne_codeAudit_219 : ∀ target : Fin 399,
    (p13CompatibilityRowsOne.getD 219 0#399).getLsb target =
      @decide (P13CodeCompatible 1
        (p13CurvatureCodes.getD 219 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 1 _ _) := by
  native_decide

theorem p13RowsTwo_codeAudit_219 : ∀ target : Fin 399,
    (p13CompatibilityRowsTwo.getD 219 0#399).getLsb target =
      @decide (P13CodeCompatible 2
        (p13CurvatureCodes.getD 219 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleDecidable 2 _ _) := by
  native_decide

end Erdos64EG.Internal

