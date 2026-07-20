import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit04A
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit04B
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit04C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_04 : ∀ right : Fin 15,
    if 0 < 4 ∧ 0 < right.1 ∧ 4 + right.1 ≤ 14 then
      flatCount 4 right.1 = profile.flatCount 4 right.1
    else flatCount 4 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_04_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_04_C ⟨4, by decide⟩

end Erdos64EG.Internal
