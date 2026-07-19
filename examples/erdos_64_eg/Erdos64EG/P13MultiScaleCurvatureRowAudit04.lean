import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `4`. -/

theorem p13MultiScaleRows_rowAudit_04 : ∀ source : Fin 399,
    row 4 source = semanticRow 4 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_04 : ∀ source target : Fin 399,
    (row 4 source).getLsb target = semanticRelation 4 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_04 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
