import Erdos64EG.CT12SparseEnvelope
import Erdos64EG.SurplusScaleSplit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Part-X pressure-to-envelope route

This module owns only the typed handoff `[20] → [125] → [126]`.  Keeping the
route after both producer modules avoids changing either independent CT
implementation and makes the dependency direction explicit.
-/

/-- Node `[126]` executed from the literal Part-X node-[125] residual.  The
strict scale inequality is retained in `previous`; CT6 and CT12 consume the
same node-[18] graph prefix, so no graph, support, or branch context is
reselected at this handoff. -/
structure VerifiedSparseEnvelopeFromPressure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (entry : SparsePressureEntryResidual ctx)
    extends Core.ExactHandoff entry where
  envelope : Core.ExactHandoff (verifiedSparseEnvelopePrefix ctx
    (verifiedSparseSurplusPrefix ctx entry.2.output.previous.residual))

noncomputable def verifiedSparseEnvelopeFromPressure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : SparsePressureEntryResidual ctx) :
    VerifiedSparseEnvelopeFromPressure ctx previous where
  toExactHandoff := Core.ExactHandoff.refl previous
  envelope := Core.ExactHandoff.refl (verifiedSparseEnvelopePrefix ctx
    (verifiedSparseSurplusPrefix ctx previous.2.output.previous.residual))

theorem verifiedSparseEnvelopeFromPressure_sameLabelPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : SparsePressureEntryResidual ctx) :
    (verifiedSparseEnvelopeFromPressure ctx previous).envelope.output.previous.1.output =
      previous.2.output.previous.residual := rfl

end Erdos64EG.Internal
