import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit14A
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit14B
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit14C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_14 : ∀ right : Fin 15,
    if 0 < 14 ∧ 0 < right.1 ∧ 14 + right.1 ≤ 14 then
      flatCount 14 right.1 = profile.flatCount 14 right.1
    else flatCount 14 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_14_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_14_C ⟨4, by decide⟩

end Erdos64EG.Internal
