import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_03 : ∀ right : Fin 15,
    if 0 < 3 ∧ 0 < right.1 ∧ 3 + right.1 ≤ 14 then
      safeCount 3 right.1 = profile.safeCount 3 right.1
    else safeCount 3 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
