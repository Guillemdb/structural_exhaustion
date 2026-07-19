import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `5`. -/

theorem p13MultiScaleRows_rowAudit_05 : ∀ source : Fin 399,
    row 5 source = semanticRow 5 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_05 : ∀ source target : Fin 399,
    (row 5 source).getLsb target = semanticRelation 5 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_05 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
