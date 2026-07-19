import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_00_C : ∀ right : Fin 5,
    if 0 < 0 ∧ 0 < right.1 + 10 ∧ 0 + (right.1 + 10) ≤ 14 then
      flatCount 0 (right.1 + 10) = profile.flatCount 0 (right.1 + 10)
    else flatCount 0 (right.1 + 10) = 0 := by
  native_decide

end Erdos64EG.Internal
