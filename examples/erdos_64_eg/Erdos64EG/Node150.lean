import Erdos64EG.Node148

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [150]: cold residual after live-hot cap failure

Node [150] consumes only the no edge of node [148].  It marks the exact
failed-cap residual while leaving all facts in the focused residual and
accumulated ledger.
-/

noncomputable def node150ColdCount {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  (p13SequentialWeightedColdWindows (Node21Context active.node18)
    active.node21.barrierRateCertificate).length

/-- Framework marker on the `[150]` cold residual edge. -/
abbrev Node150ColdMarker {V : Type u} {residual : InitialResidual V}
    (_active : Node148Active V residual)
    (_failed : Node148LiveHotFailure _active) : Type (u + 3) :=
  PUnit

abbrev Node150Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual active failed => Node150ColdMarker active failed)
    residual

noncomputable def node150ColdResidual {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148To150Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node150Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _residual active failed => Node148To150Marker active failed)
    (Next := fun _residual active failed => Node150ColdMarker active failed)
    fun _residual _active _failed _node148No => PUnit.unit

noncomputable def runInitialThroughNode150 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148To150 residual).mapYesStage
    node150ColdResidual

def node150LocalChecks : Nat := 0

theorem node150LocalChecks_eq_zero : node150LocalChecks = 0 := rfl

#print axioms node150ColdResidual
#print axioms runInitialThroughNode150

end Erdos64EG.Internal
