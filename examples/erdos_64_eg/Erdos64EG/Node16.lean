import Erdos64EG.Node15
import Erdos64EG.Shared.CT1InducedP13

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [16]: HSS closure of the node-[15] avoiding branch

This file contains only the paper-local producer for the terminal ``yes``
branch of node [15].  The predecessor stage and its ledger continuation are
intentionally supplied by the node-[15] module; no routing or node-[17]
packing data is introduced here.
-/

/-- The exact target-cycle proposition produced by HSS on node [15]'s yes
constructor. -/
abbrev Node16Target {V : Type u} {residual : InitialResidual V}
    (input : Node15Input residual) : Prop :=
  PackedTarget (Node15Context input).G

/-- HSS is the sole mathematical producer at node [16]. -/
theorem node16_hss_target {V : Type u} {residual : InitialResidual V}
    (input : Node15Input residual)
    (free : Node15P13Free residual input) :
    Node16Target input :=
  hssTarget_of_p13Free (Node15Context input) free

/-- The target just produced by HSS contradicts the inherited counterexample
avoidance certificate. -/
theorem node16_hss_closure {V : Type u} {residual : InitialResidual V}
    (input : Node15Input residual)
    (free : Node15P13Free residual input) : False :=
  (Node15Context input).avoids (node16_hss_target input free)

abbrev Node16Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionYesClosed
    (Node15Input (V := V))
    (fun _residual input => Node15P13Free _residual input)
    (fun _residual input => Node15NotP13Free _residual input)
    residual

noncomputable def node16HSSContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node15Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node16Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes
    (fun _residual input free => node16_hss_closure input free)

/-- Follow exactly the node-[15] yes edge to its terminal HSS contradiction;
the framework retains only the literal no constructor. -/
noncomputable def runInitialThroughNode16 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode15 residual).mapYesStage node16HSSContinuation

/-- The conclusion is definitionally a terminal contradiction; no work is
performed outside the finite CT1/HSS execution already certified upstream. -/
def node16LocalChecks : Nat := 0

theorem node16LocalChecks_eq_zero : node16LocalChecks = 0 := rfl

#print axioms node16_hss_closure
#print axioms node16_hss_target
#print axioms node16HSSContinuation

end Erdos64EG.Internal
