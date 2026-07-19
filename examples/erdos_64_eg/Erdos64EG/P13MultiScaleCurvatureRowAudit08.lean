import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

/-! Packed-row audit for connector length `8`. -/

theorem p13MultiScaleRows_rowAudit_08 : ∀ source : Fin 399,
    row 8 source = semanticRow 8 source := by
  native_decide

theorem p13MultiScaleRows_codeAudit_08 : ∀ source target : Fin 399,
    (row 8 source).getLsb target = semanticRelation 8 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_08 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
