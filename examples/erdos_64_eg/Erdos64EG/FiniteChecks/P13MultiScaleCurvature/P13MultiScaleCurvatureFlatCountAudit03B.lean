import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_03_B : ∀ right : Fin 5,
    if 0 < 3 ∧ 0 < right.1 + 5 ∧ 3 + (right.1 + 5) ≤ 14 then
      flatCount 3 (right.1 + 5) = profile.flatCount 3 (right.1 + 5)
    else flatCount 3 (right.1 + 5) = 0 := by
  native_decide

end Erdos64EG.Internal
