import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleSafeCounts_audit_02 : ∀ right : Fin 15,
    if 0 < 2 ∧ 0 < right.1 ∧ 2 + right.1 ≤ 14 then
      safeCount 2 right.1 = profile.safeCount 2 right.1
    else safeCount 2 right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
