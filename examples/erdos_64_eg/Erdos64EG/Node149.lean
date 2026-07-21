import Erdos64EG.Node148

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [149]: terminal live-hot density cap

Node [149] consumes only the yes edge of node [148].  The framework maps that
literal continuation to a terminal marker; all branch facts remain owned by
the focused residual and accumulated ledger.
-/

abbrev Node149Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual _active _cap => PUnit)
    residual

noncomputable def node149DensityCap {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148To149Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node149Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := fun _residual active cap => Node148To149Marker active cap)
    (Next := fun _residual _active _cap => PUnit)
    fun _residual _active _cap _node148Yes => PUnit.unit

noncomputable def runInitialThroughNode149 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148To149 residual).mapYesStage
    node149DensityCap

def node149LocalChecks : Nat := 0

theorem node149LocalChecks_eq_zero : node149LocalChecks = 0 := rfl

#print axioms node149DensityCap
#print axioms runInitialThroughNode149

end Erdos64EG.Internal
