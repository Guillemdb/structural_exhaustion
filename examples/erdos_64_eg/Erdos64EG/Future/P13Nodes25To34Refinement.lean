import Erdos64EG.Future.P13Node32To33
import Erdos64EG.Future.P13Node32To34
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Core.ZeroWorkBudget

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Framework-accumulated execution of nodes [25]--[34]

The mathematical node payloads remain the existing paper-specific structures.
This module replaces their repeated application-level predecessor plumbing by
one stable residual and `Core.ResidualRefinement.State.StageNode`.  Every stage
is definitionally the same existing node output, and node [32] retains exactly
the two original rank-loss/full-rank edges.
-/

/-- Stable carrier selected at the completed node-[24] handoff. -/
structure P13Node24RefinementResidual where
  ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}
  node21 : VerifiedP13MultiScaleCurvaturePrefix ctx
  node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21

namespace P13Node24RefinementResidual

noncomputable def node25 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node25LargeRemainder
      residual.ctx residual.node21 residual.node24 :=
  residual.node24.node25

noncomputable def node26 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node26RemainderContinuation
      residual.ctx residual.node21 residual.node24 :=
  residual.node25.node26

noncomputable def node27 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node27NoInternalThreeCore
      residual.ctx residual.node21 residual.node24 residual.node26 :=
  residual.node26.node27

noncomputable def node28 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node28PositiveDeficiency
      residual.ctx residual.node21 residual.node24 residual.node26
        residual.node27 :=
  residual.node27.node28

noncomputable def node29 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node29ExternalIncidenceSupply
      residual.ctx residual.node21 residual.node24 residual.node26
        residual.node27 residual.node28 :=
  residual.node28.node29

noncomputable def node30 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node30WedgeLower
      residual.ctx residual.node21 residual.node24 residual.node26
        residual.node27 residual.node28 residual.node29 :=
  residual.node29.node30

noncomputable def node31 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node31CurvatureTargetRank
      residual.ctx residual.node21 residual.node24 residual.node26
        residual.node27 residual.node28 residual.node29 residual.node30 :=
  residual.node30.node31

noncomputable def node32 (residual : P13Node24RefinementResidual.{u}) :
    VerifiedP13Node32RankDecision
      residual.ctx residual.node21 residual.node24 residual.node26
        residual.node27 residual.node28 residual.node29 residual.node30
        residual.node31 :=
  residual.node31.node32

end P13Node24RefinementResidual

/-! ## Automatic node-[24] entry

Node `[24]` contributes its mathematical output as the first accumulated
stage in this refinement segment. `StageNode.run` performs the ledger update;
there is no application-authored checkpoint or detached carrier attachment.
-/

abbrev P13Node24Stage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node24

noncomputable def p13Node24Entry :
    Core.ResidualRefinement.State.StageNode
      (facts := []) P13Node24Stage :=
  Core.ResidualRefinement.State.StageNode.exact
    P13Node24RefinementResidual.node24

/-- Each certificate is the framework's exact-output carrier at the stable
residual. Earlier certificates live in the accumulated fact bundle. -/
abbrev P13Node25Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node25

abbrev P13Node26Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node26

abbrev P13Node27Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node27

abbrev P13Node28Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node28

abbrev P13Node29Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node29

/-- Node `[29]`'s reusable surplus-adjusted incidence ceiling, stated once at
its producer and inherited by all later accumulated branches. -/
abbrev P13Node29SurplusAdjustedSupplyFact
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  (p13RemainderCurvatureProfile residual.ctx).positiveDeficiency -
      Graph.InducedPathWindowLedger.remainderSurplus residual.ctx.G.object ≤
    15 * Graph.InducedPathWindowLedger.packingNumber residual.ctx.G.object +
      Graph.InducedPathWindowLedger.totalSurplus residual.ctx.G.object

instance : Core.ResidualRefinement.State.StageEntails
    P13Node29Stage P13Node29SurplusAdjustedSupplyFact where
  prove stage := by
    exact stage.output.surplusAdjustedSupply.trans <|
      (Nat.sub_le _ _).trans <|
        Nat.add_le_add_left stage.output.windowSurplus_le_total _

abbrev P13Node30Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node30

abbrev P13Node31Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node31

abbrev P13Node32Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ExactHandoff residual.node32

noncomputable def p13Node25Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node24Stage) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) P13Node25Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Previous := fun (residual : P13Node24RefinementResidual.{u}) =>
      VerifiedP13Node24FiniteDensityHandoff residual.ctx residual.node21)
    (expected := fun (residual : P13Node24RefinementResidual.{u}) =>
      residual.node24)
    (fun _residual
      (node24 : VerifiedP13Node24FiniteDensityHandoff _ _) =>
        node24.node25)

noncomputable def p13Node26Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node25Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node26Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node25)
    (fun _residual previous => previous.node26)

noncomputable def p13Node27Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node26Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node27Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node26)
    (fun _residual previous => previous.node27)

noncomputable def p13Node28Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node27Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node28Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node27)
    (fun _residual previous => previous.node28)

noncomputable def p13Node29Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node28Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node29Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node28)
    (fun _residual previous => previous.node29)

noncomputable def p13Node30Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node29Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node30Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node29)
    (fun _residual previous => previous.node30)

noncomputable def p13Node31Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node30Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node31Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node30)
    (fun _residual previous => previous.node31)

noncomputable def p13Node32Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node31Stage) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node32Stage :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (Residual := P13Node24RefinementResidual)
    (expected := fun residual => residual.node31)
    (fun _residual previous => previous.node32)

abbrev P13Node24Facts :=
  [Core.ResidualRefinement.State.Available P13Node24Stage]
abbrev P13Node25Facts :=
  Core.ResidualRefinement.State.Available P13Node25Stage ::
    P13Node24Facts
abbrev P13Node26Facts :=
  Core.ResidualRefinement.State.Available P13Node26Stage :: P13Node25Facts
abbrev P13Node27Facts :=
  Core.ResidualRefinement.State.Available P13Node27Stage :: P13Node26Facts
abbrev P13Node28Facts :=
  Core.ResidualRefinement.State.Available P13Node28Stage :: P13Node27Facts
abbrev P13Node29Facts :=
  Core.ResidualRefinement.State.Available P13Node29Stage :: P13Node28Facts
abbrev P13Node30Facts :=
  Core.ResidualRefinement.State.Available P13Node30Stage :: P13Node29Facts
abbrev P13Node31Facts :=
  Core.ResidualRefinement.State.Available P13Node31Stage :: P13Node30Facts
abbrev P13Node32Facts :=
  Core.ResidualRefinement.State.Available P13Node32Stage :: P13Node31Facts

noncomputable def p13Node24State
    (residual : P13Node24RefinementResidual.{u}) :=
  p13Node24Entry.run
    (Core.ResidualRefinement.State.initial residual)

noncomputable def p13Node25State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node25Refinement.run (p13Node24State residual)

noncomputable def p13Node26State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node26Refinement.run (p13Node25State residual)

noncomputable def p13Node27State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node27Refinement.run (p13Node26State residual)

noncomputable def p13Node28State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node28Refinement.run (p13Node27State residual)

noncomputable def p13Node29State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node29Refinement.run (p13Node28State residual)

noncomputable def p13Node30State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node30Refinement.run (p13Node29State residual)

noncomputable def p13Node31State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node31Refinement.run (p13Node30State residual)

noncomputable def p13Node32State (residual : P13Node24RefinementResidual.{u}) :=
  p13Node32Refinement.run (p13Node31State residual)

abbrev P13Node32RankDrop (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13CurvatureTargetRank residual.ctx <
    (p13RemainderCurvatureProfile residual.ctx).wedgeCount

abbrev P13Node32FullRank (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13CurvatureTargetRank residual.ctx =
    (p13RemainderCurvatureProfile residual.ctx).wedgeCount

noncomputable def p13Node32Decision :
    Core.ResidualRefinement.State.DecisionNode (facts := P13Node32Facts)
      P13Node32RankDrop P13Node32FullRank := by
  simpa [P13Node32RankDrop, P13Node32FullRank] using
    (Core.ResidualRefinement.State.DecisionNode.ltOrEqUsingStage
      (Residual := P13Node24RefinementResidual)
      (facts := P13Node32Facts) (Required := P13Node31Stage)
      (fun residual => p13CurvatureTargetRank residual.ctx)
      (fun residual =>
        (p13RemainderCurvatureProfile residual.ctx).wedgeCount)
      (fun _state node31 => node31.output.targetRankUpper))

structure P13Node33Stage (residual : P13Node24RefinementResidual.{u}) where
  rankDrop : P13Node32RankDrop residual
  output : VerifiedP13Node33RankReducingDependence
    residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
      residual.node28 residual.node29 residual.node30 residual.node31
      residual.node32 rankDrop

structure P13Node34Stage (residual : P13Node24RefinementResidual.{u}) where
  fullRank : P13Node32FullRank residual
  output : VerifiedP13Node34FullCurvatureRank
    residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
      residual.node28 residual.node29 residual.node30 residual.node31
      residual.node32 fullRank

noncomputable def p13Node33Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node32RankDrop facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node32Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node33Stage :=
  Core.ResidualRefinement.State.StageNode.usingFactAndExactStage
    (required := P13Node32RankDrop)
    (expected := P13Node24RefinementResidual.node32)
    (Next := fun residual rankDrop previous =>
      VerifiedP13Node33RankReducingDependence
        residual.ctx residual.node21 residual.node24 residual.node26
          residual.node27 residual.node28 residual.node29 residual.node30
          residual.node31 previous rankDrop)
    (fun _residual rankDrop previous => previous.node33 rankDrop)
    (fun _residual rankDrop output => ⟨rankDrop, output⟩)

noncomputable def p13Node34Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains P13Node32FullRank facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node32Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node34Stage :=
  Core.ResidualRefinement.State.StageNode.usingFactAndExactStage
    (required := P13Node32FullRank)
    (expected := P13Node24RefinementResidual.node32)
    (Next := fun residual fullRank previous =>
      VerifiedP13Node34FullCurvatureRank
        residual.ctx residual.node21 residual.node24 residual.node26
          residual.node27 residual.node28 residual.node29 residual.node30
          residual.node31 previous fullRank)
    (fun _residual fullRank previous => previous.node34 fullRank)
    (fun _residual fullRank output => ⟨fullRank, output⟩)

/-- Execute the existing node-[32] dichotomy and refine both original edges.
There is no third result constructor and the residual carrier is unchanged. -/
noncomputable def p13Nodes25To34Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Node32Decision.run (p13Node32State residual)).mapStages
    p13Node33Refinement p13Node34Refinement

theorem p13Node32State_retains_residual
    (residual : P13Node24RefinementResidual.{u}) :
    (p13Node32State residual).residual = residual :=
  rfl

theorem p13Nodes25To34Run_exact
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To34Run residual with
    | .yesBranch branch =>
        Nonempty (P13Node33Stage branch.state.residual) ∧
          branch.state.residual = residual
    | .noBranch branch =>
        Nonempty (P13Node34Stage branch.state.residual) ∧
          branch.state.residual = residual := by
  unfold p13Nodes25To34Run
  cases p13Node32Decision.run (p13Node32State residual) with
  | yesBranch branch =>
      exact ⟨(branch.runStage p13Node33Refinement).state.latest,
        (branch.runStage p13Node33Refinement).residualExact.trans
          (p13Node32State_retains_residual residual)⟩
  | noBranch branch =>
      exact ⟨(branch.runStage p13Node34Refinement).state.latest,
        (branch.runStage p13Node34Refinement).residualExact.trans
          (p13Node32State_retains_residual residual)⟩

/-- The migration adds no primitive inspection beyond the mathematical node
work already certified by the retained outputs. -/
def p13Nodes25To34RefinementBudget
    (residual : P13Node24RefinementResidual.{u}) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero
    (fun _ => residual.ctx.G.object.input.vertices.card)

theorem p13Nodes25To34Refinement_polynomial
    (residual : P13Node24RefinementResidual.{u}) :
    (p13Nodes25To34RefinementBudget residual).checks () ≤
      (p13Nodes25To34RefinementBudget residual).coefficient *
        ((p13Nodes25To34RefinementBudget residual).size () + 1) ^
          (p13Nodes25To34RefinementBudget residual).degree :=
  (p13Nodes25To34RefinementBudget residual).bounded ()

#print axioms p13Node32State_retains_residual
#print axioms p13Nodes25To34Run_exact
#print axioms p13Nodes25To34Refinement_polynomial

end Erdos64EG.Internal
