import Erdos64EG.Node152
import StructuralExhaustion.Graph.InducedPathColdCorridor

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [153]: framework first-failure scan for cold branch-excess stubs

Node [153] consumes the exact node-[152] branch-excess residual.  For each
literal selected stub it runs the graph-owned first-failure machine.  The
semantic F2/F3/F5 promotion work beyond this scan must be produced by later
framework stages from this exact residual; it is not assumed by this node.
-/

theorem node153_minimality_dart_not_bridge
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  packedStaticInput.not_isBridge (by decide) ctx dart

def node153CorridorProducer {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    InducedPathColdCorridor.Producer (Node21Context active.node18).G.object where
  notBridge := node153_minimality_dart_not_bridge (Node21Context active.node18)

theorem node153RunFirstFailure_total {V : Type u}
    {residual : InitialResidual V} {active : Node148Active V residual}
    (entry : InducedPathColdCorridor.CubicStub
      (Node21Context active.node18).G.object) :
    (∃ hit data,
      InducedPathColdCorridor.runFirstFailure
        (node153CorridorProducer active) PowerOfTwoLength
        powerOfTwoLengthDecidable entry = .first hit data) ∨
    (∃ noEvent germ,
      InducedPathColdCorridor.runFirstFailure
        (node153CorridorProducer active) PowerOfTwoLength
        powerOfTwoLengthDecidable entry = .germ noEvent germ) :=
  InducedPathColdCorridor.runFirstFailure_total
    (node153CorridorProducer active) PowerOfTwoLength
    powerOfTwoLengthDecidable entry

theorem node153EveryScheduledFirstFailure_total {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    ∀ entry ∈ node152BranchExcessSchedule active,
      (∃ hit data,
        InducedPathColdCorridor.runFirstFailure
          (node153CorridorProducer active) PowerOfTwoLength
          powerOfTwoLengthDecidable entry = .first hit data) ∨
      (∃ noEvent germ,
        InducedPathColdCorridor.runFirstFailure
          (node153CorridorProducer active) PowerOfTwoLength
          powerOfTwoLengthDecidable entry = .germ noEvent germ) :=
  fun entry _member => node153RunFirstFailure_total entry

abbrev Node153Stage {V : Type u} (_residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
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
    _residual

noncomputable def node153ColdFirstFailureRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node152Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node153Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _residual active _failed =>
      { branchExcessCount : Nat //
        branchExcessCount = (node152BranchExcessSchedule active).length ∧
        13 * node150ColdCount active ≤
          branchExcessCount +
            13 * (node151ColdNonCubicWindows active).length })
    (Next := fun _residual active _failed =>
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
    fun _residual active _failed node152 => by
      refine
        ⟨node152.1, node152.2.1,
          node153EveryScheduledFirstFailure_total active⟩

noncomputable def runInitialThroughNode153 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode152 residual).mapYesStage
    node153ColdFirstFailureRefinement

def node153LocalChecks : Nat := 0

theorem node153LocalChecks_eq_zero : node153LocalChecks = 0 := rfl

end Erdos64EG.Internal
