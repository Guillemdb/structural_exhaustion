import Erdos64EG.Node45

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [46]: rank-drop branch closed

Node [45] has proved that the admitted whole-carrier quotient code is
injective.  The exact node-[35] CT15 circuit retained on the same live leaf
contains two distinct raw coordinates with equal quotient code.  Node [46]
combines precisely those two statements and closes only that leaf.  Every
already handled sibling is retained by Core as terminal bypass data.
-/

abbrev Node46Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoClosed
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active) residual

/-- The sole local contradiction at node [46]. -/
theorem node46WholeRankDropImpossible {V : Type u}
    {residual : InitialResidual V} (active : Node41Active V residual)
    (whole : Node41Whole active) (node45 : Node45Output active whole) : False :=
  active.data.output.circuit.distinct
    (node45.exactRawLabels active.data.output.circuit.identified)

/-- Framework-owned closure of the live node-[45] leaf. -/
noncomputable def node46P13RankDropClosure {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node45Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node46Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchNoContinuation
    (fun _ active whole node45 =>
      node46WholeRankDropImpossible active whole node45)

noncomputable def runInitialThroughNode46 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode45 residual).mapYesStage
    node46P13RankDropClosure

def node46LocalChecks : Nat := 0

theorem node46LocalChecks_eq_zero : node46LocalChecks = 0 := rfl

#print axioms node46WholeRankDropImpossible
#print axioms node46P13RankDropClosure
#print axioms runInitialThroughNode46

end Erdos64EG.Internal
