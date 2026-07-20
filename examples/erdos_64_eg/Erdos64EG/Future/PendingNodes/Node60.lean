import Erdos64EG.Future.PendingNodes.Node59

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [60]: net-cap contradiction

Node [60] closes only node [59]'s nonnegative constructor.  The literal
node-[57] strict-quarter inequality and node-[58] exact charge are retained
inside the framework active carrier, so no fact is rederived or requested
from a sibling branch.  Core preserves every earlier bypass and exposes only
node [59]'s strict-negative constructor to node [61].
-/

theorem node60P13NetCapImpossible {V : Type u}
    {residual : InitialResidual V} (active : Node59Active residual)
    (nonnegative : Node59Nonnegative residual active) : False := by
  have strictNat := active.data.output.strictQuarter
  have strictReal :
      (4 * node56NetDeficiencyNumerator active.data.data : ℝ) <
        (p13RemainderVertices
          (Node21Context active.data.data.data.previous)).card := by
    exact_mod_cast strictNat
  change 0 ≤ active.output.netCharge at nonnegative
  rw [active.output.netChargeExact] at nonnegative
  unfold node58NetCharge at nonnegative
  nlinarith

abbrev Node60Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
    (Node54Bypass V) (@Node59Active V)
    (@Node59Nonnegative V) (@Node59Negative V) residual

/-- Eliminate exactly the node-[59] yes leaf by the local net-cap
contradiction. -/
noncomputable def node60P13NetCapContradiction {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node59Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node60Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
    (fun _residual active nonnegative =>
      node60P13NetCapImpossible active nonnegative)

noncomputable def runInitialThroughNode60 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (node56Input : Node56NetCapTypedYellowInput V)
    (node57Input : Node57StrictQuarterTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode59 quietBlock node48Input
    node52Input node54Input node56Input node57Input residual).mapYesStage
      node60P13NetCapContradiction

def node60LocalChecks : Nat := 0

theorem node60LocalChecks_eq_zero : node60LocalChecks = 0 := rfl

#print axioms node60P13NetCapImpossible
#print axioms node60P13NetCapContradiction
#print axioms runInitialThroughNode60

end Erdos64EG.Internal
