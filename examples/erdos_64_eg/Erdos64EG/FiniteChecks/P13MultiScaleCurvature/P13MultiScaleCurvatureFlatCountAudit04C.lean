import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_04_C : ∀ right : Fin 5,
    if 0 < 4 ∧ 0 < right.1 + 10 ∧ 4 + (right.1 + 10) ≤ 14 then
      flatCount 4 (right.1 + 10) = profile.flatCount 4 (right.1 + 10)
    else flatCount 4 (right.1 + 10) = 0 := by
  native_decide

end Erdos64EG.Internal
