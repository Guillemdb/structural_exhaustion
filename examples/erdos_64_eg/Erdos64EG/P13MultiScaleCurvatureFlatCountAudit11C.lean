import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_11_C : ∀ right : Fin 5,
    if 0 < 11 ∧ 0 < right.1 + 10 ∧ 11 + (right.1 + 10) ≤ 14 then
      flatCount 11 (right.1 + 10) = profile.flatCount 11 (right.1 + 10)
    else flatCount 11 (right.1 + 10) = 0 := by
  native_decide

end Erdos64EG.Internal
