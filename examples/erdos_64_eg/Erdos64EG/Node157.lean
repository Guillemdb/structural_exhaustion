import Erdos64EG.Node156

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [157]: G3 first-failure refinement

Node [157] consumes the literal G3 continuation emitted by node [156].  The
current predecessor ledger has ruled out F1 and F4 on every scheduled cold
corridor, while the graph-owned first-failure profile has F2 and F3 empty.
This node therefore refines the live G3 leaf to the exact `.germ` outcome for
every scheduled entry.  No CT3 compression is asserted here: the finite
same-interface table and replacement candidate data must be supplied by a
later framework CT3 instantiation on this residual.
-/

abbrev Node157AllScheduledGerms {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (_g3 : Node156G3Silent active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ noEvent germ,
        InducedPathColdCorridor.runFirstFailure
          (node153CorridorProducer active.data.data) PowerOfTwoLength
          powerOfTwoLengthDecidable entry = .germ noEvent germ

abbrev Node157Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
      (Node154Bypass V) (Node154LiveLeaf V)
      (@Node154G1Hit V) (@Node154NoG1 V))
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    (@Node157AllScheduledGerms V) residual

noncomputable def node157G3FirstFailureRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node156Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node157Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := @Node156G3Output V)
    (Next := @Node157AllScheduledGerms V)
    fun _residual active _g3 node156 => by
      intro entry member
      have noF1 :
          ¬∃ vertex ∈
            (node153CorridorProducer active.data.data).stages entry |>.values,
              InducedPathColdCorridor.F1
                (node153CorridorProducer active.data.data) PowerOfTwoLength
                entry vertex :=
        active.output entry member
      have noF4 :
          ¬∃ vertex ∈
            (node153CorridorProducer active.data.data).stages entry |>.values,
              InducedPathColdCorridor.F4 entry vertex :=
        node156 entry member
      have total := node153RunFirstFailure_total
        (active := active.data.data) entry
      rcases total with ⟨hit, data, hrun⟩ | ⟨noEvent, germ, hrun⟩
      · exfalso
        cases data with
        | f1 proof _ =>
            exact noF1 ⟨hit.value, hit.member, proof⟩
        | f2 _ proof _ =>
            exact proof.elim
        | f3 _ _ proof _ =>
            exact proof.elim
        | f4 _ _ _ proof _ =>
            exact noF4 ⟨hit.value, hit.member, proof⟩
      · exact ⟨noEvent, germ, hrun⟩

noncomputable def runInitialThroughNode157 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode156 residual).mapYesStage
    node157G3FirstFailureRefinement

theorem node157_everyScheduledGerm {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (g3 : Node156G3Silent active)
    (_output : Node157AllScheduledGerms active g3) :
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ noEvent germ,
        InducedPathColdCorridor.runFirstFailure
          (node153CorridorProducer active.data.data) PowerOfTwoLength
          powerOfTwoLengthDecidable entry = .germ noEvent germ :=
  _output

def node157LocalChecks : Nat := 0

theorem node157LocalChecks_eq_zero : node157LocalChecks = 0 := rfl

#print axioms node157G3FirstFailureRefinement
#print axioms runInitialThroughNode157

end Erdos64EG.Internal
