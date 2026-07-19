import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_06_B : ∀ right : Fin 5,
    if 0 < 6 ∧ 0 < right.1 + 5 ∧ 6 + (right.1 + 5) ≤ 14 then
      flatCount 6 (right.1 + 5) = profile.flatCount 6 (right.1 + 5)
    else flatCount 6 (right.1 + 5) = 0 := by
  native_decide

end Erdos64EG.Internal
