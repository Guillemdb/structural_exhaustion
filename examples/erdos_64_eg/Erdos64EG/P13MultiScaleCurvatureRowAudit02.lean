import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `2`. -/

theorem p13MultiScaleRows_rowAudit_02 : ∀ source : Fin 399,
    row 2 source = semanticRow 2 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_02 : ∀ source target : Fin 399,
    (row 2 source).getLsb target = semanticRelation 2 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_02 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
