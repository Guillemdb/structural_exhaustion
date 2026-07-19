import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `11`. -/

theorem p13MultiScaleRows_rowAudit_11 : ∀ source : Fin 399,
    row 11 source = semanticRow 11 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_11 : ∀ source target : Fin 399,
    (row 11 source).getLsb target = semanticRelation 11 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_11 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
