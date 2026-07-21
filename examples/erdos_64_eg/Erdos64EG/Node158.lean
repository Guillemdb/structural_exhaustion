import Erdos64EG.Node157
import StructuralExhaustion.Graph.InducedPathColdGermScale

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

/-!
# Diagram node [158]: bounded same-interface promotion of G3 germs

This auxiliary implementation node consumes the exact node-[157] G3 germ
residual.  For each scheduled germ it executes the graph-owned cold-germ scale
split at the ambient vertex-cardinality scale.  The long branch contradicts
the `ColdStructuralGerm.supportBound` carried by the graph producer, so the
live residual is a bounded same-interface residual for every scheduled entry.
-/

abbrev Node158Scale {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) : Nat :=
  (Node21Context active.data.data.node18).G.object.input.vertices.card

abbrev Node158BoundedSameInterfaceOutput {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (_g3 : Node156G3Silent active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ noEvent, ∃ germ,
        InducedPathColdCorridor.runFirstFailure
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            powerOfTwoLengthDecidable entry = .germ noEvent germ ∧
        ∃ bounded :
          BoundedSameInterfaceResidual
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active),
          InducedPathColdGermScale.route
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active) = .short bounded

abbrev Node158Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
      (Node154Bypass V) (Node154LiveLeaf V)
      (@Node154G1Hit V) (@Node154NoG1 V))
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    (@Node158BoundedSameInterfaceOutput V) residual

noncomputable def node158BoundedSameInterfaceRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node157Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node158Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _residual active g3 =>
      Node157AllScheduledGerms active g3)
    (Next := fun _residual active g3 =>
      Node158BoundedSameInterfaceOutput active g3)
    fun _residual active g3 node157 => by
      intro entry member
      rcases node157 entry member with ⟨noEvent, germ, hrun⟩
      let routed := InducedPathColdGermScale.route
          (node153CorridorProducer active.data.data) PowerOfTwoLength
          entry germ (Node158Scale active)
      cases hroute : routed with
      | short bounded =>
          exact ⟨noEvent, ⟨germ, ⟨hrun, ⟨bounded, hroute⟩⟩⟩⟩
      | long longResidual =>
          have supportBound :
              ((node153CorridorProducer active.data.data).ambientReturn
                  entry).support.length ≤ Node158Scale active := by
            simpa [Node158Scale] using germ.supportBound
          exact (Nat.not_lt_of_ge supportBound longResidual.exceeds).elim

noncomputable def runInitialThroughNode158 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode157 residual).mapYesStage
    node158BoundedSameInterfaceRefinement

theorem node158_everyScheduledBounded {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (g3 : Node156G3Silent active)
    (output : Node158BoundedSameInterfaceOutput active g3) :
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ noEvent, ∃ germ,
        InducedPathColdCorridor.runFirstFailure
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            powerOfTwoLengthDecidable entry = .germ noEvent germ ∧
        ∃ bounded :
          BoundedSameInterfaceResidual
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active),
          InducedPathColdGermScale.route
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active) = .short bounded :=
  output

def node158LocalChecks : Nat := 0

theorem node158LocalChecks_eq_zero : node158LocalChecks = 0 := rfl

#print axioms node158BoundedSameInterfaceRefinement
#print axioms runInitialThroughNode158

end Erdos64EG.Internal
