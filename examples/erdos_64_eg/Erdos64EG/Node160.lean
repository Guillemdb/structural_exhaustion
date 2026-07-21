import Erdos64EG.Node159

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [160]: binary CT3 terminal split

Node [160] consumes the exact node-[159] CT3-refined G3 residual and uses a
framework focused decision to split the live branch.  The yes branch is the
case where every scheduled CT3 run lands in one of CT3's compression-style
terminals.  The no branch retains a concrete scheduled entry whose CT3 run is
one of CT3's residual terminals, distinguishing or novel.
-/

abbrev Node160Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
    (Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
      (Node154Bypass V) (Node154LiveLeaf V)
      (@Node154G1Hit V) (@Node154NoG1 V))
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)

abbrev Node160Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationActive
    (Node156Active V) (@Node156G3Silent V) (@Node159CT3Output V)

abbrev Node160AllCompressionOrKnown {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual) : Prop :=
  ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
    (node159Run active.data entry).terminal = .compression ∨
      (node159Run active.data entry).terminal = .knownRow

abbrev Node160HasCT3Residual {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual) : Prop :=
  ¬Node160AllCompressionOrKnown active

abbrev Node160DecisionStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V) residual

noncomputable def node160CT3TerminalDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node159Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node160DecisionStage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
    (Bypass :=
      Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
        (Node154Bypass V) (Node154LiveLeaf V)
        (@Node154G1Hit V) (@Node154NoG1 V))
    (Active := Node156Active V)
    (yes := @Node156G2Event V)
    (no := @Node156G3Silent V)
    (Output := @Node159CT3Output V)
    (nextYes := @Node160AllCompressionOrKnown V)
    (nextNo := @Node160HasCT3Residual V)
    (fun _residual active => Classical.propDecidable
      (Node160AllCompressionOrKnown active))
    (fun _residual _active absent => absent)

abbrev Node160CT3ResidualOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_hasResidual : Node160HasCT3Residual active) : Prop :=
    ∃ entry ∈ node152BranchExcessSchedule active.data.data.data,
      (node159Run active.data entry).terminal = .distinguishing ∨
        (node159Run active.data entry).terminal = .novelRow

abbrev Node160ResidualStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node160CT3ResidualOutput V) residual

noncomputable def node160CT3ResidualContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node160DecisionStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node160ResidualStage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (Bypass := Node160Bypass V)
    (Active := Node160Active V)
    (yes := @Node160AllCompressionOrKnown V)
    (no := @Node160HasCT3Residual V)
    (fun _residual active hasResidual =>
      by
        classical
        by_contra noResidualEntry
        apply hasResidual
        intro entry member
        by_cases good :
            (node159Run active.data entry).terminal = .compression ∨
              (node159Run active.data entry).terminal = .knownRow
        · exact good
        · have residualTerminal :
              (node159Run active.data entry).terminal = .distinguishing ∨
                (node159Run active.data entry).terminal = .novelRow := by
            cases terminal : (node159Run active.data entry).terminal <;>
              simp [terminal] at good ⊢
          exact (noResidualEntry ⟨entry, member, residualTerminal⟩).elim)

noncomputable def runInitialThroughNode160Decision {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode159 residual).mapYesStage
    node160CT3TerminalDecision

noncomputable def runInitialThroughNode160Residual {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode160Decision residual).mapYesStage
    node160CT3ResidualContinuation

theorem node160_exhaustive {V : Type u} {residual : InitialResidual V}
    (active : Node160Active V residual) :
    Node160AllCompressionOrKnown active ∨ Node160HasCT3Residual active := by
  classical
  exact em (Node160AllCompressionOrKnown active)

def node160LocalChecks : Nat := 0

theorem node160LocalChecks_eq_zero : node160LocalChecks = 0 := rfl

#print axioms node160CT3TerminalDecision
#print axioms node160CT3ResidualContinuation
#print axioms runInitialThroughNode160Residual

end Erdos64EG.Internal
