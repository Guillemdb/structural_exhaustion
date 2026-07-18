import Erdos64EG.P13Node146Route8Threshold
import Erdos64EG.P13ExactHotNormalization
import StructuralExhaustion.Core.WorkBudget

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [148]: exact live-hot entropy decision

This file consumes only the no payload of node `[146]`.  It performs the one
corrected total-demand comparison displayed at node `[148]`.  The already
verified recoverable hot aggregate pays the hot part.  Consequently failure of
the total cap retains an exact unpaid shortfall bounded by the cold part of the
same sequential ledger.

The two constructors below are exactly the existing edges `[148] -> [149]`
and `[148] -> [150]`.  No graph, context, state product, Boolean cube, or
ambient universe is enumerated.
-/

noncomputable def p13Node148TotalDemand
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  p13WindowDensityRateNumerator * p13 ctx *
    Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale

noncomputable def p13Node148HotDemand
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  p13WindowDensityRateNumerator *
    (p13SequentialWeightedHotWindows ctx node21).length *
    Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale

noncomputable def p13Node148ColdDemand
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  p13WindowDensityRateNumerator *
    (p13SequentialWeightedColdWindows ctx node21).length *
    Nat.log 2 ctx.G.object.input.vertices.card * p13ExactHotCertificateScale

noncomputable def p13Node148Allowance
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Nat :=
  p13SequentialPrintedSkeletonBits ctx +
    p13SequentialHotNormalizationError ctx node21

/-- The corrected node-`[148]` comparison is definitionally the corrected
finite cap already used at nodes `[22]`--`[24]`. -/
theorem p13Node148_cap_iff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13Node148TotalDemand ctx ≤ p13Node148Allowance ctx node21 ↔
      P13WindowDensityFiniteCapWithError ctx node21 := by
  rfl

/-- The simultaneous recoverable product of the exact final aggregate pays
the complete hot demand. -/
theorem p13Node148_hotDemand_le_allowance
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13Node148HotDemand ctx node21 ≤ p13Node148Allowance ctx node21 := by
  exact p13SequentialHot_normalized_with_error ctx node21

/-- Exact partition of total demand into the hot and cold parts of the same
packing-order ledger. -/
theorem p13Node148_totalDemand_eq_hot_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13Node148TotalDemand ctx =
      p13Node148HotDemand ctx node21 + p13Node148ColdDemand ctx node21 := by
  have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
  unfold p13Node148TotalDemand p13Node148HotDemand p13Node148ColdDemand
  rw [← partition]
  ring

/-- The hot payment and exact partition bound the total demand by the
allowance plus the literal cold demand. -/
theorem p13Node148_totalDemand_le_allowance_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13Node148TotalDemand ctx ≤
      p13Node148Allowance ctx node21 + p13Node148ColdDemand ctx node21 := by
  rw [p13Node148_totalDemand_eq_hot_add_cold ctx node21]
  exact Nat.add_le_add_right (p13Node148_hotDemand_le_allowance ctx node21) _

/-- Yes payload on the existing edge `[148] -> [149]`. -/
structure P13Node148To149
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) : Type (u + 3) where
  previous : P13Node146To148 ctx node21
  exactPrevious : previous = node146No
  previousExact : previous.previous = p13SequentialWeightedLedger ctx node21
  theta_ge : (1 : ℚ) / 78 ≤ p13PackingTheta ctx
  aggregate : P13SequentialHotAggregate ctx node21
  aggregateExact : aggregate = p13SequentialFinalHotAggregate ctx node21
  densityCap : P13WindowDensityFiniteCapWithError ctx node21
  correctedHandoff : VerifiedP13Node24FiniteDensityHandoff ctx node21
  correctedHandoffExact : correctedHandoff.densityCap = densityCap

/-- No payload on the existing edge `[148] -> [150]`.  It retains both the
strict failure and the quantitative cold shortfall on the identical ledger. -/
structure P13Node148To150
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) : Type (u + 3) where
  previous : P13Node146To148 ctx node21
  exactPrevious : previous = node146No
  previousExact : previous.previous = p13SequentialWeightedLedger ctx node21
  theta_ge : (1 : ℚ) / 78 ≤ p13PackingTheta ctx
  aggregate : P13SequentialHotAggregate ctx node21
  aggregateExact : aggregate = p13SequentialFinalHotAggregate ctx node21
  failedCap : ¬P13WindowDensityFiniteCapWithError ctx node21
  hotPayment : p13Node148HotDemand ctx node21 ≤ p13Node148Allowance ctx node21
  totalPayment : p13Node148TotalDemand ctx ≤
    p13Node148Allowance ctx node21 + p13Node148ColdDemand ctx node21
  coldShortfall : p13Node148TotalDemand ctx - p13Node148Allowance ctx node21 ≤
    p13Node148ColdDemand ctx node21
  coldNonempty : 0 < (p13SequentialWeightedColdWindows ctx node21).length

/-- The two constructors are exactly node `[148]`'s two outgoing edges. -/
inductive P13Node148Outcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) : Type (u + 3)
  | to149 : P13Node148To149 ctx node21 node146No → P13Node148Outcome ctx node21 node146No
  | to150 : P13Node148To150 ctx node21 node146No → P13Node148Outcome ctx node21 node146No

/-- Execute node `[148]` by one corrected natural-number comparison. -/
noncomputable def runP13Node148
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) :
    P13Node148Outcome ctx node21 node146No := by
  let aggregate := p13SequentialFinalHotAggregate ctx node21
  by_cases cap : P13WindowDensityFiniteCapWithError ctx node21
  · exact .to149 {
      previous := node146No
      exactPrevious := rfl
      previousExact := node146No.previousExact
      theta_ge := node146No.theta_ge
      aggregate := aggregate
      aggregateExact := rfl
      densityCap := cap
      correctedHandoff := ⟨⟨node21, rfl⟩, cap⟩
      correctedHandoffExact := rfl
    }
  · have hotPayment := p13Node148_hotDemand_le_allowance ctx node21
    have totalPayment := p13Node148_totalDemand_le_allowance_add_cold ctx node21
    have coldShortfall :
        p13Node148TotalDemand ctx - p13Node148Allowance ctx node21 ≤
          p13Node148ColdDemand ctx node21 := by
      omega
    have overflow : VerifiedP13Node23FiniteOverflow ctx node21 :=
      ⟨⟨node21, rfl⟩, cap⟩
    exact .to150 {
      previous := node146No
      exactPrevious := rfl
      previousExact := node146No.previousExact
      theta_ge := node146No.theta_ge
      aggregate := aggregate
      aggregateExact := rfl
      failedCap := cap
      hotPayment := hotPayment
      totalPayment := totalPayment
      coldShortfall := coldShortfall
      coldNonempty := overflow.cold_nonempty
    }

theorem runP13Node148_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) :
    (∃ payload, runP13Node148 ctx node21 node146No = .to149 payload) ∨
      (∃ payload, runP13Node148 ctx node21 node146No = .to150 payload) := by
  cases runP13Node148 ctx node21 node146No with
  | to149 payload => exact Or.inl ⟨payload, rfl⟩
  | to150 payload => exact Or.inr ⟨payload, rfl⟩

/-- Node `[148]` performs one primitive comparison after reusing the already
verified local hot-product accounting. -/
def p13Node148LocalCheckCount
    (_ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat := 1

theorem p13Node148LocalCheckCount_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13Node148LocalCheckCount ctx ≤
      (ctx.G.object.input.vertices.card + 1) ^ 1 := by
  simp [p13Node148LocalCheckCount]

def p13Node148WorkBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.constant
    (fun _ => ctx.G.object.input.vertices.card) 1

@[simp] theorem p13Node148WorkBudget_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13Node148WorkBudget ctx).checks () = p13Node148LocalCheckCount ctx := by
  rfl

end Erdos64EG.Internal
