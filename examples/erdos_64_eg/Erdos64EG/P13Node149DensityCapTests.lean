import Erdos64EG.P13Node149DensityCap

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148Yes : P13Node148To149 ctx node21 node146No) :
    let node149 := verifiedP13Node149DensityCap node148Yes
    p13WindowDensityRateNumerator * p13 ctx *
          Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale ≤
        p13SequentialPrintedSkeletonBits ctx +
          p13SequentialHotNormalizationError ctx node21 := by
  let node149 := verifiedP13Node149DensityCap node148Yes
  exact node149.correctedThetaCap

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148Yes : P13Node148To149 ctx node21 node146No)
    (hn : 5 ≤ ctx.G.object.input.vertices.card) :
    (p13 ctx : ℝ) / ctx.G.object.input.vertices.card ≤
      p13Node149ThetaWindow +
        p13Node149ThetaError ctx.G.object.input.vertices.card := by
  exact (verifiedP13Node149DensityCap node148Yes).theta_le_thetaWindow_add_oOne hn

#print axioms verifiedP13Node149DensityCap
#print axioms VerifiedP13Node149DensityCap.correctedThetaCap
#print axioms VerifiedP13Node149DensityCap.correctedRemainderCap
#print axioms p13Node149ThetaError_tendsto_zero
#print axioms p13Node149ThetaWindow_eq_exact
#print axioms VerifiedP13Node149DensityCap.theta_le_thetaWindow_add_oOne

end Erdos64EG.Internal
