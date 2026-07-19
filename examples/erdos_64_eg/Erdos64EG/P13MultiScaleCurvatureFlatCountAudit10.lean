import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit10A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit10B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit10C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_10 : ∀ right : Fin 15,
    if 0 < 10 ∧ 0 < right.1 ∧ 10 + right.1 ≤ 14 then
      flatCount 10 right.1 = profile.flatCount 10 right.1
    else flatCount 10 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_10_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_10_C ⟨4, by decide⟩

end Erdos64EG.Internal
