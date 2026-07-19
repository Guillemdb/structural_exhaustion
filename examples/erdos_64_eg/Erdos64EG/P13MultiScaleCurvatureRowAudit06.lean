import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `6`. -/

theorem p13MultiScaleRows_rowAudit_06 : ∀ source : Fin 399,
    row 6 source = semanticRow 6 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_06 : ∀ source target : Fin 399,
    (row 6 source).getLsb target = semanticRelation 6 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_06 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
