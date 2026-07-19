import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `14`. -/

theorem p13MultiScaleRows_rowAudit_14 : ∀ source : Fin 399,
    row 14 source = semanticRow 14 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_14 : ∀ source target : Fin 399,
    (row 14 source).getLsb target = semanticRelation 14 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_14 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
