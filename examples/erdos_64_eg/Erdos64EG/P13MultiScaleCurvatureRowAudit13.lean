import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `13`. -/

theorem p13MultiScaleRows_rowAudit_13 : ∀ source : Fin 399,
    row 13 source = semanticRow 13 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_13 : ∀ source target : Fin 399,
    (row 13 source).getLsb target = semanticRelation 13 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_13 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
