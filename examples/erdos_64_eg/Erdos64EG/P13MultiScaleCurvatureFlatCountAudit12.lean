import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit12A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit12B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit12C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_12 : ∀ right : Fin 15,
    if 0 < 12 ∧ 0 < right.1 ∧ 12 + right.1 ≤ 14 then
      flatCount 12 right.1 = profile.flatCount 12 right.1
    else flatCount 12 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_12_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_12_C ⟨4, by decide⟩

end Erdos64EG.Internal
