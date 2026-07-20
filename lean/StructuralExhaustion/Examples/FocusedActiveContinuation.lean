import StructuralExhaustion.Core.FocusedActiveContinuation

namespace StructuralExhaustion.Examples.FocusedActiveContinuation

open StructuralExhaustion

abbrev FixtureResidual := Nat
abbrev FixtureBypass (_ : FixtureResidual) : Type := PUnit
abbrev FixtureActive (_ : FixtureResidual) : Type := Nat
abbrev FixtureFirst (_ : FixtureResidual) (_ : Nat) : Type := Nat
abbrev FixtureMapped (_ : FixtureResidual) (_ : Nat) : Type := Nat

abbrev FixtureFirstStage :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    FixtureBypass FixtureActive FixtureFirst

abbrev FixtureMappedStage :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    FixtureBypass FixtureActive FixtureMapped

def fixtureInitial :
    Core.ResidualRefinement.State FixtureResidual [] :=
  Core.ResidualRefinement.State.initial 3

noncomputable def fixtureFirstNode :
    Core.ResidualRefinement.State.StageNode (facts := [])
      FixtureFirstStage where
  produce := fun state => .active state.residual (state.residual + 1)

noncomputable def fixtureAfterFirst := fixtureFirstNode.run fixtureInitial

noncomputable def fixtureMappedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixtureFirstStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureMappedStage :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchActiveContinuation
    (Bypass := FixtureBypass) (Active := FixtureActive)
    (Current := FixtureFirst) (Next := FixtureMapped)
    fun _residual _data current => current + 1

noncomputable def fixtureAfterMapped := fixtureMappedNode.run fixtureAfterFirst

abbrev FixtureSecondActive :=
  Core.ResidualRefinement.State.FocusedBranchActiveData
    FixtureActive FixtureMapped

abbrev FixtureSecond (residual : FixtureResidual)
    (_ : FixtureSecondActive residual) : Type := Nat

abbrev FixtureSecondStage :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    FixtureBypass FixtureSecondActive FixtureSecond

noncomputable def fixtureSecondNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixtureMappedStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureSecondStage :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchActiveAgain
    (Bypass := FixtureBypass) (Active := FixtureActive)
    (Current := FixtureMapped) (Next := FixtureSecond)
    fun _residual _data current => current + 1

noncomputable def fixtureAfterSecond := fixtureSecondNode.run fixtureAfterMapped

abbrev FixtureDecisionActive :=
  Core.ResidualRefinement.State.FocusedBranchActiveData
    FixtureSecondActive FixtureSecond

abbrev FixtureYes (residual : FixtureResidual)
    (_ : FixtureDecisionActive residual) : Prop :=
  False

abbrev FixtureNo (residual : FixtureResidual)
    (_ : FixtureDecisionActive residual) : Prop :=
  True

abbrev FixtureDecisionStage :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    FixtureBypass FixtureDecisionActive FixtureYes FixtureNo

noncomputable def fixtureDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixtureSecondStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureDecisionStage :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchActiveContinuation
    (Bypass := FixtureBypass) (Active := FixtureSecondActive)
    (Current := FixtureSecond) (yes := FixtureYes) (no := FixtureNo)
    (fun _residual _data _current => Classical.propDecidable False)
    (fun _residual _data _current _absent => True.intro)

noncomputable def fixtureAfterDecision :=
  fixtureDecisionNode.run fixtureAfterSecond

abbrev FixtureClosed :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
    FixtureBypass FixtureDecisionActive FixtureYes FixtureNo

noncomputable def fixtureCloseNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixtureDecisionStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureClosed :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
    (Bypass := FixtureBypass) (Active := FixtureDecisionActive)
    (yes := FixtureYes) (no := FixtureNo)
    fun _residual _data impossible => impossible.elim

noncomputable def fixtureAfterClose := fixtureCloseNode.run fixtureAfterDecision

abbrev FixtureClosedActive :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosedActive
    FixtureDecisionActive FixtureNo

abbrev FixtureFinal (residual : FixtureResidual)
    (_ : FixtureClosedActive residual) : Type := PUnit

abbrev FixtureFinalStage :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    FixtureBypass FixtureClosedActive FixtureFinal

noncomputable def fixtureFinalNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixtureClosed) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureFinalStage :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchDecisionYesClosed
    (Bypass := FixtureBypass) (Active := FixtureDecisionActive)
    (yes := FixtureYes) (no := FixtureNo) (Output := FixtureFinal)
    fun _residual _data _proof => PUnit.unit

noncomputable def fixtureAfterFinal := fixtureFinalNode.run fixtureAfterClose

theorem allFocusedStagesAccumulate :
    Nonempty (FixtureMappedStage fixtureAfterFinal.residual) ∧
      Nonempty (FixtureClosed fixtureAfterFinal.residual) := by
  exact ⟨fixtureAfterFinal.require
      (property := Core.ResidualRefinement.State.Available FixtureMappedStage),
    fixtureAfterFinal.require
      (property := Core.ResidualRefinement.State.Available FixtureClosed)⟩

#print axioms allFocusedStagesAccumulate

end StructuralExhaustion.Examples.FocusedActiveContinuation
