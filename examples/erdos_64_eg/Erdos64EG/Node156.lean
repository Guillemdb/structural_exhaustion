import Erdos64EG.Node154

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [156]: G2/G3 split below no-G1

Node [156] consumes the literal no-G1 continuation emitted by node [154].
Core focuses that live leaf and decides whether a scheduled cold corridor has
the graph-owned F4 event.  The yes branch is the paper's G2 event residual.
The no branch is the exact G3 residual consumed by node [157]; it proves only
the absence of G2 on the same scheduled stubs.
-/

abbrev Node156Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
    (Node154Bypass V) (Node154LiveLeaf V)
    (@Node154G1Hit V) (@Node154NoG1 V)

abbrev Node156Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationActive
    (Node154LiveLeaf V) (@Node154NoG1 V) (@Node154NoG1Output V)

abbrev Node156G2Event {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) : Prop :=
  ∃ entry ∈ node152BranchExcessSchedule active.data.data,
    ∃ vertex ∈ (node153CorridorProducer active.data.data).stages entry |>.values,
      InducedPathColdCorridor.F4 entry vertex

abbrev Node156G3Silent {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) : Prop :=
  ¬Node156G2Event active

abbrev Node156G3Output {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) (_g3 : Node156G3Silent active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ¬∃ vertex ∈
        (node153CorridorProducer active.data.data).stages entry |>.values,
          InducedPathColdCorridor.F4 entry vertex

abbrev Node156G2HotHandoffOutput {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (_g2 : Node156G2Event active) : Prop :=
    ∃ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ vertex ∈
        (node153CorridorProducer active.data.data).stages entry |>.values,
        ∃ handoff :
          InducedPathColdCorridor.Producer.SurplusHandoff
            (node153CorridorProducer active.data.data),
          handoff.stub = entry ∧ handoff.vertex = vertex

abbrev Node156DecisionStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node156Bypass V)
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    residual

abbrev Node156Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node156Bypass V)
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    (@Node156G3Output V) residual

abbrev Node156G2HotHandoffStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node156Bypass V)
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    (@Node156G2HotHandoffOutput V) residual

noncomputable def node156G2G3Decision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node154Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
    (@Node156DecisionStage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
    (Bypass := Node154Bypass V)
    (Active := Node154LiveLeaf V)
    (yes := @Node154G1Hit V)
    (no := @Node154NoG1 V)
    (Output := @Node154NoG1Output V)
    (nextYes := @Node156G2Event V)
    (nextNo := @Node156G3Silent V)
    (fun _residual active => Classical.propDecidable
      (Node156G2Event active))
    (fun _residual _active absent => absent)

noncomputable def node156G3Continuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node156DecisionStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
    (@Node156Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (Bypass := Node156Bypass V)
    (Active := Node156Active V)
    (yes := @Node156G2Event V)
    (no := @Node156G3Silent V)
    (fun _residual active noG2 =>
      by
        intro entry member targetEvent
        apply noG2
        rcases targetEvent with ⟨vertex, stageMember, proof⟩
        exact ⟨entry, member, vertex, stageMember, proof⟩)

noncomputable def node156G2HotHandoffContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node156DecisionStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
    (@Node156G2HotHandoffStage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    (Bypass := Node156Bypass V)
    (Active := Node156Active V)
    (yes := @Node156G2Event V)
    (no := @Node156G3Silent V)
    (fun _residual active g2 =>
      by
        rcases g2 with ⟨entry, member, vertex, stageMember, high⟩
        exact
          ⟨entry, member, vertex, stageMember,
            InducedPathColdCorridor.surplusHandoffOfF4
              (node153CorridorProducer active.data.data) entry vertex high,
            rfl, rfl⟩)

noncomputable def runInitialThroughNode156Decision {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode154 residual).mapYesStage
    node156G2G3Decision

noncomputable def runInitialThroughNode156 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode156Decision residual).mapYesStage
    node156G3Continuation

noncomputable def runInitialThroughNode156G2HotHandoff {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode156Decision residual).mapYesStage
    node156G2HotHandoffContinuation

theorem node156_exhaustive {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) :
    Node156G2Event active ∨ Node156G3Silent active := by
  classical
  exact em (Node156G2Event active)

def node156LocalChecks : Nat := 0

theorem node156LocalChecks_eq_zero : node156LocalChecks = 0 := rfl

#print axioms node156G2G3Decision
#print axioms node156G3Continuation
#print axioms node156G2HotHandoffContinuation
#print axioms runInitialThroughNode156
#print axioms runInitialThroughNode156G2HotHandoff

end Erdos64EG.Internal
