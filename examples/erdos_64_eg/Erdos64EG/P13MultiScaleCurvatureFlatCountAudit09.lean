import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit09A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit09B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit09C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_09 : ∀ right : Fin 15,
    if 0 < 9 ∧ 0 < right.1 ∧ 9 + right.1 ≤ 14 then
      flatCount 9 right.1 = profile.flatCount 9 right.1
    else flatCount 9 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_09_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_09_C ⟨4, by decide⟩

end Erdos64EG.Internal
