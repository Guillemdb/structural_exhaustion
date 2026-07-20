import Erdos64EG.Future.P13Node146Route8Threshold
import Erdos64EG.Future.P13ExactHotNormalization
import StructuralExhaustion.Core.ResidualRefinement
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
    (_node146No : P13Node146To148 ctx node21) : Type (u + 3) where
  densityCap : P13WindowDensityFiniteCapWithError ctx node21

/-- No payload on the existing edge `[148] -> [150]`.  It retains both the
strict failure and the quantitative cold shortfall on the identical ledger. -/
structure P13Node148To150
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (_node146No : P13Node146To148 ctx node21) : Type (u + 3) where
  failedCap : ¬P13WindowDensityFiniteCapWithError ctx node21
  hotPayment : p13Node148HotDemand ctx node21 ≤ p13Node148Allowance ctx node21
  totalPayment : p13Node148TotalDemand ctx ≤
    p13Node148Allowance ctx node21 + p13Node148ColdDemand ctx node21
  coldShortfall : p13Node148TotalDemand ctx - p13Node148Allowance ctx node21 ≤
    p13Node148ColdDemand ctx node21
  coldNonempty : 0 < (p13SequentialWeightedColdWindows ctx node21).length

/-! ## Framework-owned node-[148] decision

The node-[146] no payload and node-[145] ledger remain in the incoming
state.  These declarations add only the cap decision and its new branch
payload; neither branch copies an inherited field.
-/

abbrev P13Node148Cap (residual : P13Node145RefinementResidual.{u}) : Prop :=
  P13WindowDensityFiniteCapWithError residual.ctx residual.node21

abbrev P13Node148FailedCap
    (residual : P13Node145RefinementResidual.{u}) : Prop :=
  ¬P13WindowDensityFiniteCapWithError residual.ctx residual.node21

noncomputable def p13Node148DecisionRefinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node146To148Stage) facts] :
    Core.ResidualRefinement.State.DecisionNode (facts := facts)
      P13Node148Cap P13Node148FailedCap :=
  Core.ResidualRefinement.State.DecisionNode.complement _
    (fun _state => Classical.propDecidable _)

abbrev P13Node148To149Stage (residual : P13Node145RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node146To148Stage
    (fun residual node146No =>
      P13Node148To149 residual.ctx residual.node21 node146No) residual

abbrev P13Node148To150Stage (residual : P13Node145RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node146To148Stage
    (fun residual node146No =>
      P13Node148To150 residual.ctx residual.node21 node146No) residual

noncomputable def p13Node148To149Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node148Cap facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node146To148Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node148To149Stage :=
  Core.ResidualRefinement.State.StageNode.usingFactAndStage
    (required := P13Node148Cap) (Required := P13Node146To148Stage)
    (fun _state cap node146No => ⟨node146No, ⟨cap⟩⟩)

noncomputable def p13Node148To150Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node148FailedCap facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node146To148Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node148To150Stage :=
  Core.ResidualRefinement.State.StageNode.usingFactAndStage
    (required := P13Node148FailedCap) (Required := P13Node146To148Stage)
    (fun state failedCap node146No => by
      have hotPayment :=
        p13Node148_hotDemand_le_allowance state.residual.ctx state.residual.node21
      have totalPayment :=
        p13Node148_totalDemand_le_allowance_add_cold
          state.residual.ctx state.residual.node21
      have coldShortfall :
          p13Node148TotalDemand state.residual.ctx -
              p13Node148Allowance state.residual.ctx state.residual.node21 ≤
            p13Node148ColdDemand state.residual.ctx state.residual.node21 := by
        omega
      have coldNonempty :
          0 < (p13SequentialWeightedColdWindows
            state.residual.ctx state.residual.node21).length := by
        by_contra absent
        have empty : (p13SequentialWeightedColdWindows
            state.residual.ctx state.residual.node21).length = 0 :=
          Nat.eq_zero_of_not_pos absent
        apply failedCap
        apply (p13Node148_cap_iff
          state.residual.ctx state.residual.node21).mp
        simpa [p13Node148ColdDemand, empty] using totalPayment
      exact ⟨node146No,
        { failedCap := failedCap
          hotPayment := hotPayment
          totalPayment := totalPayment
          coldShortfall := coldShortfall
          coldNonempty := coldNonempty }⟩)

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
