import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit05A
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit05B
import Erdos64EG.P13MultiScaleCurvatureFlatCountAudit05C

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleFlatCounts_audit_05 : ∀ right : Fin 15,
    if 0 < 5 ∧ 0 < right.1 ∧ 5 + right.1 ≤ 14 then
      flatCount 5 right.1 = profile.flatCount 5 right.1
    else flatCount 5 right.1 = 0 := by
  intro right
  fin_cases right
  · simpa using p13MultiScaleFlatCounts_audit_05_A ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_A ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_A ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_A ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_A ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_B ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_B ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_B ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_B ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_B ⟨4, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_C ⟨0, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_C ⟨1, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_C ⟨2, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_C ⟨3, by decide⟩
  · simpa using p13MultiScaleFlatCounts_audit_05_C ⟨4, by decide⟩

end Erdos64EG.Internal
