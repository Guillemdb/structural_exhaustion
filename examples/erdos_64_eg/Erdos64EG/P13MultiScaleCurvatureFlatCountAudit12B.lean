import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_12_B : ∀ right : Fin 5,
    if 0 < 12 ∧ 0 < right.1 + 5 ∧ 12 + (right.1 + 5) ≤ 14 then
      flatCount 12 (right.1 + 5) = profile.flatCount 12 (right.1 + 5)
    else flatCount 12 (right.1 + 5) = 0 := by
  native_decide

end Erdos64EG.Internal
