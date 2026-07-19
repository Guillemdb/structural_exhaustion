import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      safeCount 0 right.1 = profile.safeCount 0 right.1
    else safeCount 0 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
