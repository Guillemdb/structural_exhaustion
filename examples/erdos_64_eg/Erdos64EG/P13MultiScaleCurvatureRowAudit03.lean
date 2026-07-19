import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `3`. -/

theorem p13MultiScaleRows_rowAudit_03 : ∀ source : Fin 399,
    row 3 source = semanticRow 3 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_03 : ∀ source target : Fin 399,
    (row 3 source).getLsb target = semanticRelation 3 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_03 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
