import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_09 : ∀ right : Fin 15,
    if 0 < 9 ∧ 0 < right.1 ∧ 9 + right.1 ≤ 14 then
      safeCount 9 right.1 = profile.safeCount 9 right.1
    else safeCount 9 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
