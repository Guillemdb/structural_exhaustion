import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `1`. -/

theorem p13MultiScaleRows_rowAudit_01 : ∀ source : Fin 399,
    row 1 source = semanticRow 1 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_01 : ∀ source target : Fin 399,
    (row 1 source).getLsb target = semanticRelation 1 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_01 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
