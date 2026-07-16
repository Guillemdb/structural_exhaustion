import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Independent audit shard for connector length `8`. -/

theorem p13MultiScaleRows_codeAudit_08 : ∀ source target : Fin 399,
    (row 8 source).getLsb target =
      @decide (P13CodeCompatibleSparse 8
        (p13CurvatureCodes.getD source.1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleSparseDecidable 8 _ _) := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_08 : ∀ right : Fin 15,
    if 0 < 8 ∧ 0 < right.1 ∧ 8 + right.1 ≤ 14 then
      safeCount 8 right.1 = profile.safeCount 8 right.1
    else safeCount 8 right.1 = 0 := by
  native_decide

theorem p13MultiScaleFlatCounts_audit_08 : ∀ right : Fin 15,
    if 0 < 8 ∧ 0 < right.1 ∧ 8 + right.1 ≤ 14 then
      flatCount 8 right.1 = profile.flatCount 8 right.1
    else flatCount 8 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
