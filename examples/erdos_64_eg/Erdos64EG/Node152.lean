import Erdos64EG.Node151
import StructuralExhaustion.Graph.InducedPathColdBranchExcess

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdBranchExcess
open StructuralExhaustion.Graph.InducedPathColdLedger

universe u

/-!
# Diagram node [152]: branch-excess stubs of the retained cold windows

Node [152] consumes the node-[151] ambient-cubic cold residual and applies the
graph-owned branch-excess selection to every retained cold window.  Each
retained ambient-cubic P13 contributes exactly thirteen literal excess stubs.
 -/

theorem node152BranchExcessEntries_length {V : Type u}
    {residual : InitialResidual V} {active : Node148Active V residual}
    (window : { cold : P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate //
        AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) }) :
    (branchExcessStubs (Node21Context active.node18).G.object
      (node151WindowIndex active window.1.window) window.2).length = 13 :=
  branchExcessStubs_length_eq_thirteen (Node21Context active.node18).G.object
    (node151WindowIndex active window.1.window) window.2

theorem node152BranchExcessEntries_nodup {V : Type u}
    {residual : InitialResidual V} {active : Node148Active V residual}
    (window : { cold : P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate //
        AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) }) :
    (branchExcessStubs (Node21Context active.node18).G.object
      (node151WindowIndex active window.1.window) window.2).Nodup :=
  branchExcessStubs_nodup (Node21Context active.node18).G.object
    (node151WindowIndex active window.1.window) window.2

noncomputable def node152BranchExcessSchedule {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    List (InducedPathColdCorridor.CubicStub
      (Node21Context active.node18).G.object) :=
  (node151ColdCubicWindows active).flatMap fun window =>
    branchExcessStubs (Node21Context active.node18).G.object
      (node151WindowIndex active window.1.window) window.2

theorem node152BranchExcessSchedule_length {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    (node152BranchExcessSchedule active).length =
      13 * (node151ColdCubicWindows active).length := by
  unfold node152BranchExcessSchedule
  rw [List.length_flatMap]
  simp only [node152BranchExcessEntries_length]
  rw [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  exact Nat.mul_comm _ _

theorem node152_thirteen_mul_cold_le_branchExcess_add_nonCubic {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    13 * node150ColdCount active ≤
      (node152BranchExcessSchedule active).length +
        13 * (node151ColdNonCubicWindows active).length := by
  rw [node152BranchExcessSchedule_length]
  have partition := node151Cold_cubic_nonCubic_length active
  omega

abbrev Node152Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual active _failed =>
      { branchExcessCount : Nat //
        branchExcessCount = (node152BranchExcessSchedule active).length ∧
        13 * node150ColdCount active ≤
          branchExcessCount +
            13 * (node151ColdNonCubicWindows active).length })
    residual

noncomputable def node152BranchExcessRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node151Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
    (@Node152Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun residual active failed =>
      { loss : Nat //
        loss = (node151ColdNonCubicWindows active).length ∧
        loss ^ 2 ≤ node19SurplusCoefficient *
          (Node21Context active.node18).G.object.input.vertices.card ∧
        ∃ cubicCount,
          cubicCount = (node151ColdCubicWindows active).length ∧
          cubicCount + loss = node150ColdCount active })
    (Next := fun residual active failed =>
      { branchExcessCount : Nat //
        branchExcessCount = (node152BranchExcessSchedule active).length ∧
        13 * node150ColdCount active ≤
          branchExcessCount +
            13 * (node151ColdNonCubicWindows active).length })
    fun _residual active _failed _node151 => by
      refine
        ⟨(node152BranchExcessSchedule active).length, rfl, ?_⟩
      exact node152_thirteen_mul_cold_le_branchExcess_add_nonCubic active

noncomputable def runInitialThroughNode152 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode151 residual).mapYesStage
    node152BranchExcessRefinement

def node152LocalChecks : Nat := 0

theorem node152LocalChecks_eq_zero : node152LocalChecks = 0 := rfl

end Erdos64EG.Internal
