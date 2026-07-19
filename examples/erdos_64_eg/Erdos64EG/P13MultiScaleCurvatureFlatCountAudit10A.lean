import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_10_A : ∀ right : Fin 5,
    if 0 < 10 ∧ 0 < right.1 + 0 ∧ 10 + (right.1 + 0) ≤ 14 then
      flatCount 10 (right.1 + 0) = profile.flatCount 10 (right.1 + 0)
    else flatCount 10 (right.1 + 0) = 0 := by
  native_decide

end Erdos64EG.Internal
