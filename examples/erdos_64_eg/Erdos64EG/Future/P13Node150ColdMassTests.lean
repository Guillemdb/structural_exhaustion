import Erdos64EG.Future.P13Node150ColdMass

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  {node146No : P13Node146To148 ctx node21}
  (node148 : P13Node148To150 ctx node21 node146No)

example : 0 < (p13Node150FiniteColdMass node148).coldCount :=
  (p13Node150FiniteColdMass node148).coldNonempty

example : p13Route8ColdMassNumerator = 1108581006 := by simp

example : p13NegativeNetColdMassNumerator = 8608581006 := by simp

example : p13ManuscriptRoute8ColdMassNumerator = 4875590826119 := by simp

example : p13ManuscriptNegativeNetColdMassNumerator = 37860939659399 := by simp

example :
    (120334838333602 : ℚ) / 10 ^ 18 <
      p13ManuscriptRoute8ColdMassCoefficient :=
  p13ManuscriptRoute8ColdMassCoefficient_printedBracket.1

example :
    (998452154807083 : ℚ) / 10 ^ 18 <
      p13ManuscriptNegativeNetColdMassCoefficient :=
  p13ManuscriptNegativeNetColdMassCoefficient_printedBracket.1

example :
    Filter.Tendsto
      (fun n : Nat => p13ManuscriptDyadicHotNormalizationRealEnvelope n /
        ((n : ℝ) * (Nat.log 2 n : ℝ)))
      Filter.atTop (nhds 0) :=
  (p13Node150FiniteColdMass node148).normalizationVanishing

example : p13Node150LocalCheckCount (p13Node150FiniteColdMass node148) ≤
    (ctx.G.object.input.vertices.card + 1) ^ 1 :=
  p13Node150LocalCheckCount_polynomial _

example : (p13Node150WorkBudget ctx).checks () = 0 := rfl

#print axioms p13Node150_route8ColdMassCrossMultiplied
#print axioms p13Node150_negativeNetColdMassCrossMultiplied
#print axioms p13Route8ColdMassCoefficient_finiteDecimalBracket
#print axioms p13NegativeNetColdMassCoefficient_finiteDecimalBracket
#print axioms p13ExactManuscriptHotRateCertificate
#print axioms p13ExactManuscriptDyadicRateCertificate
#print axioms p13SequentialHot_manuscriptDyadic_normalized_with_error
#print axioms p13Node150_manuscriptRoute8ColdMassCrossMultiplied
#print axioms p13Node150_manuscriptNegativeNetColdMassCrossMultiplied
#print axioms p13ManuscriptRoute8ColdMassCoefficient_printedBracket
#print axioms p13ManuscriptNegativeNetColdMassCoefficient_printedBracket
#print axioms p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero
#print axioms p13Node150LocalCheckCount_polynomial
#print axioms p13Node150WorkBudget_checks

end Erdos64EG.Internal
