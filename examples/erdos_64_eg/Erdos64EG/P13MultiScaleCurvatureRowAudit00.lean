import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `0`. -/

theorem p13MultiScaleRows_rowAudit_00 : ∀ source : Fin 399,
    row 0 source = semanticRow 0 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_00 : ∀ source target : Fin 399,
    (row 0 source).getLsb target = semanticRelation 0 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_00 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
