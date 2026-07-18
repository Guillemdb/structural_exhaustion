import Erdos64EG.P13ExactHotNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

example
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13SequentialHotScaleLoss ctx node21 ≤
      30 * (p13SequentialWeightedHotWindows ctx node21).length :=
  p13SequentialHotScaleLoss_le ctx node21

example
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 +
        p13WindowDensityRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale :=
  p13SequentialTotal_normalized_le_error_add_cold ctx node21

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23FiniteOverflow ctx node21) :
    0 < (p13SequentialWeightedColdWindows ctx node21).length :=
  node23.cold_nonempty

example
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (∃ node23, runP13Node22FiniteDensityDecision ctx node21 = .tooLarge node23) ∨
      (∃ node24, runP13Node22FiniteDensityDecision ctx node21 = .withinCap node24) :=
  runP13Node22FiniteDensityDecision_exhaustive ctx node21

end Erdos64EG.Internal
