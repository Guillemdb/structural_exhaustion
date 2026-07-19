import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit02A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit02B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit02C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_02 : ∀ right : Fin 15,
    if 0 < 2 ∧ 0 < right.1 ∧ 2 + right.1 ≤ 14 then
      flatCount 2 right.1 = profile.flatCount 2 right.1
    else flatCount 2 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_02_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_02_C ⟨4, by decide⟩

end Erdos64EG.Internal
