import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `10`. -/

theorem p13MultiScaleRows_rowAudit_10 : ∀ source : Fin 399,
    row 10 source = semanticRow 10 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_10 : ∀ source target : Fin 399,
    (row 10 source).getLsb target = semanticRelation 10 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_10 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
