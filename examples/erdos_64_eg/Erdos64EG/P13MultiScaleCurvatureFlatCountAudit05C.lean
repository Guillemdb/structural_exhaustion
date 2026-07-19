import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_05_C : ∀ right : Fin 5,
    if 0 < 5 ∧ 0 < right.1 + 10 ∧ 5 + (right.1 + 10) ≤ 14 then
      flatCount 5 (right.1 + 10) = profile.flatCount 5 (right.1 + 10)
    else flatCount 5 (right.1 + 10) = 0 := by
  native_decide

end Erdos64EG.Internal
