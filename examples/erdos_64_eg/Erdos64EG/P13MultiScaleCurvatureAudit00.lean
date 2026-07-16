import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Independent audit shard for connector length `0`. -/

theorem p13MultiScaleRows_codeAudit_00 : ∀ source target : Fin 399,
    (row 0 source).getLsb target =
      @decide (P13CodeCompatibleSparse 0
        (p13CurvatureCodes.getD source.1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleSparseDecidable 0 _ _) := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      safeCount 0 right.1 = profile.safeCount 0 right.1
    else safeCount 0 right.1 = 0 := by
  native_decide

theorem p13MultiScaleFlatCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      flatCount 0 right.1 = profile.flatCount 0 right.1
    else flatCount 0 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
