import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit01A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit01B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit01C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_01 : ∀ right : Fin 15,
    if 0 < 1 ∧ 0 < right.1 ∧ 1 + right.1 ≤ 14 then
      flatCount 1 right.1 = profile.flatCount 1 right.1
    else flatCount 1 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_01_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_01_C ⟨4, by decide⟩

end Erdos64EG.Internal
