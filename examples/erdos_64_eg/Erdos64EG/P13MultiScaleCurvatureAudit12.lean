import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Independent audit shard for connector length `12`. -/

theorem p13MultiScaleRows_codeAudit_12 : ∀ source target : Fin 399,
    (row 12 source).getLsb target =
      @decide (P13CodeCompatibleSparse 12
        (p13CurvatureCodes.getD source.1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleSparseDecidable 12 _ _) := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_12 : ∀ right : Fin 15,
    if 0 < 12 ∧ 0 < right.1 ∧ 12 + right.1 ≤ 14 then
      safeCount 12 right.1 = profile.safeCount 12 right.1
    else safeCount 12 right.1 = 0 := by
  native_decide

theorem p13MultiScaleFlatCounts_audit_12 : ∀ right : Fin 15,
    if 0 < 12 ∧ 0 < right.1 ∧ 12 + right.1 ≤ 14 then
      flatCount 12 right.1 = profile.flatCount 12 right.1
    else flatCount 12 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
