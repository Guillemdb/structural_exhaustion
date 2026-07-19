import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `9`. -/

theorem p13MultiScaleRows_rowAudit_09 : ∀ source : Fin 399,
    row 9 source = semanticRow 9 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_09 : ∀ source target : Fin 399,
    (row 9 source).getLsb target = semanticRelation 9 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_09 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
