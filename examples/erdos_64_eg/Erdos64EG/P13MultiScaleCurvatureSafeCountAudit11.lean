import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_11 : ∀ right : Fin 15,
    if 0 < 11 ∧ 0 < right.1 ∧ 11 + right.1 ≤ 14 then
      safeCount 11 right.1 = profile.safeCount 11 right.1
    else safeCount 11 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
