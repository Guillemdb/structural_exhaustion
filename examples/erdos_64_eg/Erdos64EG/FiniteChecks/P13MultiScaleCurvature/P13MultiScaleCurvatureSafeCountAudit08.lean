import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleSafeCounts_audit_08 : ∀ right : Fin 15,
    if 0 < 8 ∧ 0 < right.1 ∧ 8 + right.1 ≤ 14 then
      safeCount 8 right.1 = profile.safeCount 8 right.1
    else safeCount 8 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
