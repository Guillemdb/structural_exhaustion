import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_08_A : ∀ right : Fin 5,
    if 0 < 8 ∧ 0 < right.1 + 0 ∧ 8 + (right.1 + 0) ≤ 14 then
      flatCount 8 (right.1 + 0) = profile.flatCount 8 (right.1 + 0)
    else flatCount 8 (right.1 + 0) = 0 := by
  native_decide

end Erdos64EG.Internal
