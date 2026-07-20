import Erdos64EG.Future.P13Node24DensityArithmetic

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 :=
  node24.thetaWindowCorrected

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
      p13SequentialPrintedSkeletonBits ctx +
        p13SequentialHotNormalizationError ctx node21 +
        p13WindowDensityRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale :=
  node24.sequentialHotColdAccounting

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21) :
    node24.localCheckCount ≤
      (ctx.G.object.input.vertices.card + 1) ^ 2 :=
  node24.localCheckCount_polynomial

#print axioms VerifiedP13Node24FiniteDensityHandoff.thetaWindowCorrected
#print axioms VerifiedP13Node24FiniteDensityHandoff.sequentialHotColdAccounting
#print axioms VerifiedP13Node24FiniteDensityHandoff.remainderCorrected
#print axioms VerifiedP13Node24FiniteDensityHandoff.seventyThreePackingCorrected

end Erdos64EG.Internal
