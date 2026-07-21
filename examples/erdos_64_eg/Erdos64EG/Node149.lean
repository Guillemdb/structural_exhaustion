import Erdos64EG.Node148

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [149]: terminal live-hot density cap

Node [149] consumes only the yes edge of node [148].  The framework maps that
literal continuation to the terminal density-cap payload; all predecessor
branches and the accumulated ledger remain owned by Core.
-/

/-- The terminal node-[149] payload: exactly the cap selected at node [148]. -/
structure Node149DensityCap {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual)
    (_node148Yes : Node148To149 active) : Type (u + 3) where
  densityCap : Node148LiveHotCap active
  totalDemandExact :
    node148TotalDemand active =
      node148HotDemand active + node148ColdDemand active

abbrev Node149Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun residual active cap =>
      Node149DensityCap (residual := residual) active
        (Node148To149.mk cap (node148_totalDemand_eq_hot_add_cold active)))
    residual

noncomputable def node149DensityCap {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148To149Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node149Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    fun _residual active _cap (node148Yes : Node148To149 active) =>
      { densityCap := node148Yes.densityCap
        totalDemandExact := node148Yes.totalDemandExact }

noncomputable def runInitialThroughNode149 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148To149 residual).mapYesStage
    node149DensityCap

def node149LocalChecks : Nat := 0

theorem node149LocalChecks_eq_zero : node149LocalChecks = 0 := rfl

#print axioms node149DensityCap
#print axioms runInitialThroughNode149

end Erdos64EG.Internal
