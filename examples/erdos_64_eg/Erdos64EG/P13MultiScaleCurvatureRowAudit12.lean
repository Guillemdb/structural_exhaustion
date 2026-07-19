import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `12`. -/

theorem p13MultiScaleRows_rowAudit_12 : ∀ source : Fin 399,
    row 12 source = semanticRow 12 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_12 : ∀ source target : Fin 399,
    (row 12 source).getLsb target = semanticRelation 12 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_12 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
