import Erdos64EG.Future.P13HighEntropyRemainderBits
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-! ## Reusable mathematical entailments stored by the accumulated stages -/

/-- Node `[24]`'s exact finite window-density inequality. -/
abbrev P13Node24WindowDensityFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13WindowDensityRateNumerator * p13 residual.ctx *
      Nat.log 2 residual.ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale ≤
    p13SequentialPrintedSkeletonBits residual.ctx +
      p13SequentialHotNormalizationError residual.ctx residual.node21

instance : Core.ResidualRefinement.State.StageEntails
    P13Node24Stage P13Node24WindowDensityFact where
  prove stage := stage.output.thetaWindowCorrected

/-- Node `[24]`'s exact cap transported to the literal remainder scale. -/
abbrev P13Node24RemainderDensityFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13WindowRemainderRateDenominator * p13 residual.ctx *
        p13Node48NormalizationScale residual.ctx ≤
    p13WindowDensitySkeletonNumerator *
        (p13RemainderVertices residual.ctx).card *
        p13Node48NormalizationScale residual.ctx +
      p13SequentialHotNormalizationError residual.ctx residual.node21

instance : Core.ResidualRefinement.State.StageEntails
    P13Node24Stage P13Node24RemainderDensityFact where
  prove _stage := p13Node48_windowDensity_remainderForm _

/-- Node `[48]`'s exact scaled forced-curvature inequality. -/
abbrev P13Node48ForcedCurvatureFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13WindowWedgeRateNumerator *
        (p13RemainderVertices residual.ctx).card *
        p13Node48NormalizationScale residual.ctx ≤
    p13WindowRemainderRateDenominator *
          p13CurvatureTargetRank residual.ctx *
          p13Node48NormalizationScale residual.ctx +
      30 * p13SequentialHotNormalizationError
        residual.ctx residual.node21 +
      2 * p13WindowRemainderRateDenominator *
        Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object *
          p13Node48NormalizationScale residual.ctx

/-- Node `[48]`'s manuscript conclusion in curvature-cost units. -/
abbrev P13Node48CostFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13WindowForcedCurvatureCost *
      (p13RemainderVertices residual.ctx).card ≤
    p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
      p13Node48CostError residual

/-- Node `[48]`'s sharper conclusion on the inherited high-entropy edge. -/
abbrev P13Node48HighEntropyCostFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  P13Node24HighEntropyDownstreamRequirement residual.ctx residual.node21 →
    p13HighEntropyForcedCurvatureCost *
        (p13RemainderVertices residual.ctx).card ≤
      p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx +
        p13Node48CostError residual

/-- Node `[49]`'s exact entropy identity. -/
abbrev P13Node49EntropyIdentityFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13ManuscriptRemainderEntropy residual =
    Real.logb 2 (p13RemainderGraphFamilyCount residual) /
      (p13RemainderVertices residual.ctx).card

/-!
# Accumulated manuscript nodes [47]--[51]

Each definition below contributes exactly one new mathematical output.  The
framework retrieves and retains every earlier stage through the stable
node-[24] residual ledger; no application node reconstructs a predecessor or
re-proves an inherited property.
-/

abbrev P13Node47RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node34Stage
    (fun residual branch => VerifiedP13Node47FullRankResidual residual branch)
    residual

noncomputable def p13Node47Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node34Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node47RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual branch => branch.node47)

abbrev P13Node48RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node47RefinementStage
    (fun residual node47 => VerifiedP13Node48FrontierCost
      residual node47.previous node47.output)
    residual

instance : Core.ResidualRefinement.State.StageEntails
    P13Node48RefinementStage P13Node48ForcedCurvatureFact where
  prove stage := stage.output.scaledCost

instance : Core.ResidualRefinement.State.StageEntails
    P13Node48RefinementStage P13Node48CostFact where
  prove stage := stage.output.forcedCost

instance : Core.ResidualRefinement.State.StageEntails
    P13Node48RefinementStage P13Node48HighEntropyCostFact where
  prove stage := stage.output.highEntropyForcedCost

noncomputable def p13Node48Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node47RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node48RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node47 => P13Node47FullRankResidual.node48 node47.output)

abbrev P13Node49RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node48RefinementStage
    (fun residual _node48 => P13Node49Output residual)
    residual

instance : Core.ResidualRefinement.State.StageEntails
    P13Node49RefinementStage P13Node49EntropyIdentityFact where
  prove stage := stage.output.entropyExact

noncomputable def p13Node49Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node48RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node49RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun residual _node48 => p13Node49Output residual)

abbrev P13Node50RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node49RefinementStage
    (fun residual _node49 => P13Node50Output residual)
    residual

noncomputable def p13Node50Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node49RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node50RefinementStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun residual _node49 => p13Node50Output residual)

abbrev P13Node50RefinementHigh
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual) : Prop :=
  P13Node50OutputHigh residual node50.output

abbrev P13Node50RefinementLow
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual) : Prop :=
  P13Node50OutputLow residual node50.output

abbrev P13Node50RefinementDecision
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecision
    P13Node50RefinementStage
    P13Node50RefinementHigh P13Node50RefinementLow residual

noncomputable def p13Node50DecisionRefinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node50RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node50RefinementDecision :=
  Core.ResidualRefinement.State.StageNode.decideUsingStage
    (fun _residual node50 =>
      Classical.propDecidable (P13Node50RefinementHigh _ node50))
    (fun _residual node50 absent => by
      exact lt_of_not_ge absent)

abbrev P13Node51RefinementOutput
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual)
    (_high : P13Node50RefinementHigh residual node50) :=
  P13Node51Output residual

abbrev P13Node51RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecisionYesContinuation
    P13Node50RefinementStage
    P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput residual

noncomputable def p13Node51Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node50RefinementDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node51RefinementStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYes
    (fun _residual node50 high =>
      p13Node51Output node50.output high)

/-! ## One operational accumulated run

Only the original full-rank edge is refined.  The rank-drop branch and every
fact already stored on both branches are retained by `BranchResult.mapNoStage`.
-/

noncomputable def p13Nodes25To47Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To34Run residual).mapNoStage p13Node47Refinement

noncomputable def p13Nodes25To48Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To47Run residual).mapNoStage p13Node48Refinement

noncomputable def p13Nodes25To49Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To48Run residual).mapNoStage p13Node49Refinement

noncomputable def p13Nodes25To50Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To49Run residual).mapNoStage p13Node50Refinement

noncomputable def p13Nodes25To50DecisionRun
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To50Run residual).mapNoStage p13Node50DecisionRefinement

noncomputable def p13Nodes25To51Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To50DecisionRun residual).mapNoStage p13Node51Refinement

/-- The accumulated run never changes the stable node-[24] residual. -/
theorem p13Nodes25To51Run_retains_residual
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To51Run residual with
    | .yesBranch branch => branch.state.residual = residual
    | .noBranch branch => branch.state.residual = residual := by
  unfold p13Nodes25To51Run p13Nodes25To50DecisionRun p13Nodes25To50Run
    p13Nodes25To49Run p13Nodes25To48Run p13Nodes25To47Run
  cases p13Nodes25To34Run residual with
  | yesBranch branch => exact branch.residualExact
  | noBranch branch => exact branch.residualExact

/-- The only primitive work added by the migrated handoffs is the proof-level
node-[50] comparison already owned by `OrderThresholdSplit`; ledger transport
itself performs no scan. -/
def p13Nodes47To51RefinementBudget
    (residual : P13Node24RefinementResidual.{u}) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero
    (fun _ => residual.ctx.G.object.input.vertices.card)

theorem p13Nodes47To51Refinement_polynomial
    (residual : P13Node24RefinementResidual.{u}) :
    (p13Nodes47To51RefinementBudget residual).checks () ≤
      (p13Nodes47To51RefinementBudget residual).coefficient *
        ((p13Nodes47To51RefinementBudget residual).size () + 1) ^
          (p13Nodes47To51RefinementBudget residual).degree :=
  (p13Nodes47To51RefinementBudget residual).bounded ()

end Erdos64EG.Internal
