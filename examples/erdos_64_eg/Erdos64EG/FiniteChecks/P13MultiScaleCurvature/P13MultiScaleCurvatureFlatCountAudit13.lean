import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit13A
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit13B
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit13C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_13 : ∀ right : Fin 15,
    if 0 < 13 ∧ 0 < right.1 ∧ 13 + right.1 ≤ 14 then
      flatCount 13 right.1 = profile.flatCount 13 right.1
    else flatCount 13 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_13_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_13_C ⟨4, by decide⟩

end Erdos64EG.Internal
