import Erdos64EG.Node153

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [154]: first bounded-germ case split

Node [154] consumes the literal node-[153] first-failure residual.  Core
focuses the live cold branch, transports all already handled siblings, and
decides whether some scheduled first-failure run is a G1 dyadic hit.  The no
branch keeps exactly the derived no-G1 residual for the next prescribed G2/G3
split; later nodes refine the remaining framework first-failure and germ cases.
-/

abbrev Node154LiveLeaf (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationActive
    (@Node148Active V) (@Node148LiveHotFailure V)
    (fun _residual active _failed =>
      { scannedCount : Nat //
        scannedCount = (node152BranchExcessSchedule active).length ∧
        ∀ entry ∈ node152BranchExcessSchedule active,
          (∃ hit data,
            InducedPathColdCorridor.runFirstFailure
              (node153CorridorProducer active) PowerOfTwoLength
              powerOfTwoLengthDecidable entry = .first hit data) ∨
          (∃ noEvent germ,
            InducedPathColdCorridor.runFirstFailure
              (node153CorridorProducer active) PowerOfTwoLength
              powerOfTwoLengthDecidable entry = .germ noEvent germ) })

abbrev Node154G1Hit {V : Type u} {residual : InitialResidual V}
    (active : Node154LiveLeaf V residual) : Prop :=
  ∃ entry ∈ node152BranchExcessSchedule active.data,
    ∃ vertex ∈ (node153CorridorProducer active.data).stages entry |>.values,
      InducedPathColdCorridor.F1
        (node153CorridorProducer active.data) PowerOfTwoLength entry vertex

abbrev Node154NoG1 {V : Type u} {residual : InitialResidual V}
    (active : Node154LiveLeaf V residual) : Prop :=
  ¬Node154G1Hit active

abbrev Node154Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)

abbrev Node154NoG1Output {V : Type u} {residual : InitialResidual V}
    (active : Node154LiveLeaf V residual) (_noG1 : Node154NoG1 active) :=
  Sigma (fun _ : PUnit =>
    PLift (
    ∀ entry ∈ node152BranchExcessSchedule active.data,
      ¬∃ vertex ∈ (node153CorridorProducer active.data).stages entry |>.values,
        InducedPathColdCorridor.F1
          (node153CorridorProducer active.data) PowerOfTwoLength entry vertex))

abbrev Node154DecisionStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node154Bypass V)
    (Node154LiveLeaf V) (@Node154G1Hit V) (@Node154NoG1 V) residual

noncomputable def node154GermCaseDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node153Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node154DecisionStage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
    (Bypass := Node148Bypass V)
    (Active := Node148Active V)
    (yes := @Node148LiveHotCap V)
    (no := @Node148LiveHotFailure V)
    (Output := fun _residual active _failed =>
      { scannedCount : Nat //
        scannedCount = (node152BranchExcessSchedule active).length ∧
        ∀ entry ∈ node152BranchExcessSchedule active,
          (∃ hit data,
            InducedPathColdCorridor.runFirstFailure
              (node153CorridorProducer active) PowerOfTwoLength
              powerOfTwoLengthDecidable entry = .first hit data) ∨
          (∃ noEvent germ,
            InducedPathColdCorridor.runFirstFailure
              (node153CorridorProducer active) PowerOfTwoLength
              powerOfTwoLengthDecidable entry = .germ noEvent germ) })
    (nextYes := @Node154G1Hit V)
    (nextNo := @Node154NoG1 V)
    (fun _residual active => by
      classical
      exact inferInstance)
    (fun _residual _active absent => absent)

abbrev Node154Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node154Bypass V)
    (Node154LiveLeaf V) (@Node154G1Hit V) (@Node154NoG1 V)
    (@Node154NoG1Output V)
    residual

noncomputable def node154NoG1Continuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node154DecisionStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node154Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (Bypass := Node154Bypass V)
    (Active := Node154LiveLeaf V)
    (yes := @Node154G1Hit V)
    (no := @Node154NoG1 V)
    (fun _residual active noG1 =>
      ⟨PUnit.unit, ⟨by
        intro entry member targetHit
        apply noG1
        rcases targetHit with ⟨vertex, stageMember, proof⟩
        exact ⟨entry, member, vertex, stageMember, proof⟩⟩⟩)

noncomputable def runInitialThroughNode154 {V : Type u}
    (residual : InitialResidual V) :=
  ((runInitialThroughNode153 residual).mapYesStage
    node154GermCaseDecision).mapYesStage
      node154NoG1Continuation

theorem node154_exhaustive {V : Type u} {residual : InitialResidual V}
    (active : Node154LiveLeaf V residual) :
    Node154G1Hit active ∨ Node154NoG1 active := by
  classical
  exact em (Node154G1Hit active)

def node154LocalChecks : Nat := 0

theorem node154LocalChecks_eq_zero : node154LocalChecks = 0 := rfl

end Erdos64EG.Internal
