import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_14 : ∀ right : Fin 15,
    if 0 < 14 ∧ 0 < right.1 ∧ 14 + right.1 ≤ 14 then
      safeCount 14 right.1 = profile.safeCount 14 right.1
    else safeCount 14 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
