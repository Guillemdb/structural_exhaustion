import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit00A
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit00B
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureFlatCountAudit00C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 512

theorem p13MultiScaleFlatCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      flatCount 0 right.1 = profile.flatCount 0 right.1
    else flatCount 0 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_00_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_00_C ⟨4, by decide⟩

end Erdos64EG.Internal
