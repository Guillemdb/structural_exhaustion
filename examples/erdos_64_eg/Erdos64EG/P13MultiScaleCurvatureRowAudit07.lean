import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `7`. -/

theorem p13MultiScaleRows_rowAudit_07 : ∀ source : Fin 399,
    row 7 source = semanticRow 7 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_07 : ∀ source target : Fin 399,
    (row 7 source).getLsb target = semanticRelation 7 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_07 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
