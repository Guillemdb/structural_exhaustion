import Erdos64EG.P13Node148LiveHotDecision
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.ZeroWorkBudget
import Erdos64EG.P13ExactManuscriptHotRate

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [150]: exact cold-mass arithmetic

This file consumes the literal no payload of node `[148]`.  It keeps the
normalization error explicit and proves the denominator-free forms of the
paper's cold-mass lower bounds.  It does not synthesize the separate
surviving-cold-branch exclusions or near-cubic spine estimate.
-/

/-- The paper's `C`, exactly the number of rejected windows in the canonical
node-`[145]` packing-order ledger. -/
noncomputable def p13Node150ColdCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  (p13SequentialWeightedColdWindows ctx node21).length

/-- Numerator of `1/78 - theta_win` over the common denominator
`78 * 118108581006`. -/
def p13Route8ColdMassNumerator : Nat :=
  p13WindowDensityRateNumerator - 78 * p13WindowDensitySkeletonNumerator

/-- Numerator of `1/73 - theta_win` over the common denominator
`73 * 118108581006`. -/
def p13NegativeNetColdMassNumerator : Nat :=
  p13WindowDensityRateNumerator - 73 * p13WindowDensitySkeletonNumerator

def p13Route8ColdMassCoefficient : ℚ :=
  p13Route8ColdMassNumerator / (78 * p13WindowDensityRateNumerator)

def p13NegativeNetColdMassCoefficient : ℚ :=
  p13NegativeNetColdMassNumerator / (73 * p13WindowDensityRateNumerator)

@[simp] theorem p13Route8ColdMassNumerator_exact :
    p13Route8ColdMassNumerator = 1108581006 := by
  norm_num [p13Route8ColdMassNumerator, p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator]

@[simp] theorem p13NegativeNetColdMassNumerator_exact :
    p13NegativeNetColdMassNumerator = 8608581006 := by
  norm_num [p13NegativeNetColdMassNumerator, p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator]

/-- Eighteen-decimal bracket for the conservative fixed-point coefficient
actually certified by the Lean hot-rate lower bound. -/
theorem p13Route8ColdMassCoefficient_finiteDecimalBracket :
    (120334838323711 : ℚ) / 10 ^ 18 < p13Route8ColdMassCoefficient ∧
      p13Route8ColdMassCoefficient < (120334838323712 : ℚ) / 10 ^ 18 := by
  norm_num [p13Route8ColdMassCoefficient, p13Route8ColdMassNumerator,
    p13WindowDensityRateNumerator, p13WindowDensitySkeletonNumerator]

/-- Eighteen-decimal bracket for the conservative fixed-point coefficient at
the negative-net threshold. -/
theorem p13NegativeNetColdMassCoefficient_finiteDecimalBracket :
    (998452154797192 : ℚ) / 10 ^ 18 < p13NegativeNetColdMassCoefficient ∧
      p13NegativeNetColdMassCoefficient < (998452154797193 : ℚ) / 10 ^ 18 := by
  norm_num [p13NegativeNetColdMassCoefficient,
    p13NegativeNetColdMassNumerator, p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator]

/-! The following constants use the exact final dyadic exponent of the
manuscript's 42-row rate certificate.  Unlike the shorter conservative rate
above, they rigorously support both decimal lower endpoints printed in Part
XI, including the final rounded digit of the negative-net coefficient. -/

noncomputable def p13ManuscriptRoute8ColdMassNumerator : Nat :=
  p13ManuscriptDyadicRateNumerator -
    78 * p13ManuscriptDyadicSkeletonNumerator

noncomputable def p13ManuscriptNegativeNetColdMassNumerator : Nat :=
  p13ManuscriptDyadicRateNumerator -
    73 * p13ManuscriptDyadicSkeletonNumerator

noncomputable def p13ManuscriptRoute8ColdMassCoefficient : ℚ :=
  p13ManuscriptRoute8ColdMassNumerator /
    (78 * p13ManuscriptDyadicRateNumerator)

noncomputable def p13ManuscriptNegativeNetColdMassCoefficient : ℚ :=
  p13ManuscriptNegativeNetColdMassNumerator /
    (73 * p13ManuscriptDyadicRateNumerator)

@[simp] theorem p13ManuscriptRoute8ColdMassNumerator_exact :
    p13ManuscriptRoute8ColdMassNumerator = 4875590826119 := by
  norm_num [p13ManuscriptRoute8ColdMassNumerator,
    p13ManuscriptDyadicRateNumerator_exact,
    p13ManuscriptDyadicSkeletonNumerator_exact]

@[simp] theorem p13ManuscriptNegativeNetColdMassNumerator_exact :
    p13ManuscriptNegativeNetColdMassNumerator = 37860939659399 := by
  norm_num [p13ManuscriptNegativeNetColdMassNumerator,
    p13ManuscriptDyadicRateNumerator_exact,
    p13ManuscriptDyadicSkeletonNumerator_exact]

/-- The first printed Part-XI coefficient is a strict lower endpoint. -/
theorem p13ManuscriptRoute8ColdMassCoefficient_printedBracket :
    (120334838333602 : ℚ) / 10 ^ 18 <
        p13ManuscriptRoute8ColdMassCoefficient ∧
      p13ManuscriptRoute8ColdMassCoefficient <
        (120334838333603 : ℚ) / 10 ^ 18 := by
  norm_num [p13ManuscriptRoute8ColdMassCoefficient,
    p13ManuscriptRoute8ColdMassNumerator,
    p13ManuscriptDyadicRateNumerator_exact,
    p13ManuscriptDyadicSkeletonNumerator_exact]

/-- The exact dyadic slack proves that the manuscript's rounded
`0.000998452154807083` is still a strict lower endpoint. -/
theorem p13ManuscriptNegativeNetColdMassCoefficient_printedBracket :
    (998452154807083 : ℚ) / 10 ^ 18 <
        p13ManuscriptNegativeNetColdMassCoefficient ∧
      p13ManuscriptNegativeNetColdMassCoefficient <
        (998452154807084 : ℚ) / 10 ^ 18 := by
  norm_num [p13ManuscriptNegativeNetColdMassCoefficient,
    p13ManuscriptNegativeNetColdMassNumerator,
    p13ManuscriptDyadicRateNumerator_exact,
    p13ManuscriptDyadicSkeletonNumerator_exact]

/-- Elementary denominator-free rearrangement used by both displayed
thresholds. -/
private theorem coldMassCrossMultiplied
    {rate skeleton threshold packing vertices error cold scale : Nat}
    (coefficient : threshold * skeleton ≤ rate)
    (densityLower : vertices ≤ threshold * packing)
    (payment : rate * packing * scale ≤
      skeleton * vertices * scale + error + rate * cold * scale) :
    (rate - threshold * skeleton) * vertices * scale ≤
      threshold * error + threshold * rate * cold * scale := by
  have densityScaled := Nat.mul_le_mul_left (rate * scale) densityLower
  have paymentScaled := Nat.mul_le_mul_left threshold payment
  have combined :
      (rate - threshold * skeleton) * vertices * scale +
          threshold * skeleton * vertices * scale ≤
        threshold * skeleton * vertices * scale +
          (threshold * error + threshold * rate * cold * scale) := by
    calc
      _ = rate * vertices * scale := by
        calc
          _ = ((rate - threshold * skeleton) + threshold * skeleton) *
              vertices * scale := by ring
          _ = rate * vertices * scale := by
            rw [Nat.sub_add_cancel coefficient]
      _ ≤ threshold * rate * packing * scale := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using densityScaled
      _ ≤ threshold *
          (skeleton * vertices * scale + error + rate * cold * scale) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using paymentScaled
      _ = _ := by ring
  rw [Nat.add_comm ((rate - threshold * skeleton) * vertices * scale)] at combined
  exact Nat.le_of_add_le_add_left combined

/-- The exact hot/cold partition at the full 42-row dyadic rate. -/
theorem p13SequentialTotal_manuscriptDyadic_le_error_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13ManuscriptDyadicRateNumerator * p13 ctx *
        Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactManuscriptDyadicCertificateScale ≤
      p13ManuscriptDyadicPrintedSkeletonBits ctx +
        p13ManuscriptDyadicHotNormalizationError ctx node21 +
        p13ManuscriptDyadicRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale := by
  have hot := p13SequentialHot_manuscriptDyadic_normalized_with_error ctx node21
  have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
  calc
    _ = p13ManuscriptDyadicRateNumerator *
          (p13SequentialWeightedHotWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale +
        p13ManuscriptDyadicRateNumerator *
          (p13SequentialWeightedColdWindows ctx node21).length *
          Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale := by
      rw [← partition]
      ring
    _ ≤ _ := Nat.add_le_add_right hot _

/-- Exact finite route-8 cold mass using the manuscript's complete 42-row
rate certificate. -/
theorem p13Node150_manuscriptRoute8ColdMassCrossMultiplied
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148 : P13Node148To150 ctx node21 node146No) :
    p13ManuscriptRoute8ColdMassNumerator *
        ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale) ≤
      78 * p13ManuscriptDyadicHotNormalizationError ctx node21 +
        78 * p13ManuscriptDyadicRateNumerator *
          p13Node150ColdCount ctx node21 *
          (Nat.log 2 ctx.G.object.input.vertices.card *
            p13ExactManuscriptDyadicCertificateScale) := by
  apply coldMassCrossMultiplied
      (rate := p13ManuscriptDyadicRateNumerator)
      (skeleton := p13ManuscriptDyadicSkeletonNumerator)
      (threshold := 78) (packing := p13 ctx)
      (vertices := ctx.G.object.input.vertices.card)
      (error := p13ManuscriptDyadicHotNormalizationError ctx node21)
      (cold := p13Node150ColdCount ctx node21)
      (scale := Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactManuscriptDyadicCertificateScale)
  · norm_num [p13ManuscriptDyadicRateNumerator_exact,
      p13ManuscriptDyadicSkeletonNumerator_exact]
  · exact node148.previous.crossMultiplied
  · simpa [p13ManuscriptDyadicPrintedSkeletonBits,
      p13Node150ColdCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc] using
      p13SequentialTotal_manuscriptDyadic_le_error_add_cold ctx node21

/-- Exact specialization at the paper's named negative-net threshold. -/
theorem p13Node150_manuscriptNegativeNetColdMassCrossMultiplied
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148 : P13Node148To150 ctx node21 node146No)
    (thetaAtLeast : ctx.G.object.input.vertices.card ≤ 73 * p13 ctx) :
    p13ManuscriptNegativeNetColdMassNumerator *
        ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale) ≤
      73 * p13ManuscriptDyadicHotNormalizationError ctx node21 +
        73 * p13ManuscriptDyadicRateNumerator *
          p13Node150ColdCount ctx node21 *
          (Nat.log 2 ctx.G.object.input.vertices.card *
            p13ExactManuscriptDyadicCertificateScale) := by
  apply coldMassCrossMultiplied
      (rate := p13ManuscriptDyadicRateNumerator)
      (skeleton := p13ManuscriptDyadicSkeletonNumerator)
      (threshold := 73) (packing := p13 ctx)
      (vertices := ctx.G.object.input.vertices.card)
      (error := p13ManuscriptDyadicHotNormalizationError ctx node21)
      (cold := p13Node150ColdCount ctx node21)
      (scale := Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactManuscriptDyadicCertificateScale)
  · norm_num [p13ManuscriptDyadicRateNumerator_exact,
      p13ManuscriptDyadicSkeletonNumerator_exact]
  · exact thetaAtLeast
  · simpa [p13ManuscriptDyadicPrintedSkeletonBits,
      p13Node150ColdCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc] using
      p13SequentialTotal_manuscriptDyadic_le_error_add_cold ctx node21

/-- Exact finite form of
`C >= (1/78 - theta_win)n - error` on the actual node-`[148]` no edge. -/
theorem p13Node150_route8ColdMassCrossMultiplied
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148 : P13Node148To150 ctx node21 node146No) :
    p13Route8ColdMassNumerator * ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale) ≤
      78 * p13SequentialHotNormalizationError ctx node21 +
        78 * p13WindowDensityRateNumerator * p13Node150ColdCount ctx node21 *
          (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale) := by
  apply coldMassCrossMultiplied
      (rate := p13WindowDensityRateNumerator)
      (skeleton := p13WindowDensitySkeletonNumerator)
      (threshold := 78) (packing := p13 ctx)
      (vertices := ctx.G.object.input.vertices.card)
      (error := p13SequentialHotNormalizationError ctx node21)
      (cold := p13Node150ColdCount ctx node21)
      (scale := Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale)
  · norm_num [p13WindowDensityRateNumerator,
      p13WindowDensitySkeletonNumerator]
  · exact node148.previous.crossMultiplied
  · simpa [p13Node148TotalDemand, p13Node148Allowance,
      p13Node148ColdDemand, p13SequentialPrintedSkeletonBits,
      p13Node150ColdCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc] using node148.totalPayment

/-- Conditional exact evaluation at the paper's second threshold.  This does
not assert that every node-`[150]` input satisfies `theta >= 1/73`; it proves
the displayed specialization when that branch condition is present. -/
theorem p13Node150_negativeNetColdMassCrossMultiplied
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148 : P13Node148To150 ctx node21 node146No)
    (thetaAtLeast : ctx.G.object.input.vertices.card ≤ 73 * p13 ctx) :
    p13NegativeNetColdMassNumerator * ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale) ≤
      73 * p13SequentialHotNormalizationError ctx node21 +
        73 * p13WindowDensityRateNumerator * p13Node150ColdCount ctx node21 *
          (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale) := by
  apply coldMassCrossMultiplied
      (rate := p13WindowDensityRateNumerator)
      (skeleton := p13WindowDensitySkeletonNumerator)
      (threshold := 73) (packing := p13 ctx)
      (vertices := ctx.G.object.input.vertices.card)
      (error := p13SequentialHotNormalizationError ctx node21)
      (cold := p13Node150ColdCount ctx node21)
      (scale := Nat.log 2 ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale)
  · norm_num [p13WindowDensityRateNumerator,
      p13WindowDensitySkeletonNumerator]
  · exact thetaAtLeast
  · simpa [p13Node148TotalDemand, p13Node148Allowance,
      p13Node148ColdDemand, p13SequentialPrintedSkeletonBits,
      p13Node150ColdCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc] using node148.totalPayment

/-- Exact dependency-ready node-`[150]` payload.  The separate surviving
branch/spine handoff is intentionally not claimed here. -/
structure P13Node150FiniteColdMass
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21)
    (node148 : P13Node148To150 ctx node21 node146No) : Type (u + 4)
    extends Core.ExactHandoff node148 where
  coldCount : Nat
  coldCountExact : coldCount = p13Node150ColdCount ctx node21
  coldNonempty : 0 < coldCount
  route8Lower :
    p13Route8ColdMassNumerator * ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale) ≤
      78 * p13SequentialHotNormalizationError ctx node21 +
        78 * p13WindowDensityRateNumerator * coldCount *
          (Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale)
  manuscriptRoute8Lower :
    p13ManuscriptRoute8ColdMassNumerator * ctx.G.object.input.vertices.card *
        (Nat.log 2 ctx.G.object.input.vertices.card *
          p13ExactManuscriptDyadicCertificateScale) ≤
      78 * p13ManuscriptDyadicHotNormalizationError ctx node21 +
        78 * p13ManuscriptDyadicRateNumerator * coldCount *
          (Nat.log 2 ctx.G.object.input.vertices.card *
            p13ExactManuscriptDyadicCertificateScale)
  normalizationVanishing :
    Filter.Tendsto
      (fun n : Nat => p13ManuscriptDyadicHotNormalizationRealEnvelope n /
        ((n : ℝ) * (Nat.log 2 n : ℝ)))
      Filter.atTop (nhds 0)

noncomputable def p13Node150FiniteColdMass
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node146No : P13Node146To148 ctx node21}
    (node148 : P13Node148To150 ctx node21 node146No) :
    P13Node150FiniteColdMass ctx node21 node146No node148 where
  previous := node148
  previousExact := rfl
  coldCount := p13Node150ColdCount ctx node21
  coldCountExact := rfl
  coldNonempty := node148.coldNonempty
  route8Lower := p13Node150_route8ColdMassCrossMultiplied node148
  manuscriptRoute8Lower :=
    p13Node150_manuscriptRoute8ColdMassCrossMultiplied node148
  normalizationVanishing :=
    p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero

def p13Node150LocalCheckCount
    (_result : P13Node150FiniteColdMass ctx node21 node146No node148) : Nat := 0

theorem p13Node150LocalCheckCount_polynomial
    (result : P13Node150FiniteColdMass ctx node21 node146No node148) :
    p13Node150LocalCheckCount result ≤
      (ctx.G.object.input.vertices.card + 1) ^ 1 := by
  simp [p13Node150LocalCheckCount]

def p13Node150WorkBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero
    (fun _ => ctx.G.object.input.vertices.card)

@[simp] theorem p13Node150WorkBudget_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13Node150WorkBudget ctx).checks () = 0 := rfl

end Erdos64EG.Internal
