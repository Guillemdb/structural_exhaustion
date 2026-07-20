import Erdos64EG.Future.PendingNodes.Node55

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [56]: Residual C net-deficiency cap

Node [56] consumes only the literal node-[55] active leaf.  Its exact finite
cap is retained while the old node-[24]/[29] proof is migrated to indexed
ledger queries through one typed-yellow input.  Core keeps all branch indices
and the accumulated ledger; the input supplies only the old mathematical
inequality on that exact leaf.
-/

noncomputable def node56NetDeficiencyNumerator {V : Type u}
    {residual : InitialResidual V} (active : Node55ResidualC V residual) : Nat :=
  (p13RemainderCurvatureProfile
      (Node21Context active.data.previous)).positiveDeficiency -
    Graph.InducedPathWindowLedger.remainderSurplus
      (Node21Context active.data.previous).G.object

/-- Exact rational form of the manuscript constant
`tau_win = 15 theta_win / (1 - 13 theta_win)`. -/
noncomputable def node56TauWindow : ℝ :=
  (15 * (node22SkeletonRateNumerator : ℝ)) /
    ((node22WindowRateNumerator : ℝ) -
      13 * node22SkeletonRateNumerator)

/-- Exact finite error retained before the manuscript's `o(|R|)` transport. -/
noncomputable def node56NetError {V : Type u}
    {residual : InitialResidual V} (active : Node55ResidualC V residual) : ℝ :=
  Graph.InducedPathWindowLedger.totalSurplus
    (Node21Context active.data.previous).G.object

/-- Node [56]'s sole new finite payload.  Its two fields are exactly the
error-bearing normalized cap and the strict numerical gap printed in the
paper. -/
structure Node56Output {V : Type u} {residual : InitialResidual V}
    (active : Node55ResidualC V residual) : Type (u + 2) where
  netCap :
    (node56NetDeficiencyNumerator active : ℝ) ≤
      node56TauWindow *
          (p13RemainderVertices
            (Node21Context active.data.previous)).card +
        node56NetError active
  limitingCapStrict : node56TauWindow < (1 / 4 : ℝ)

/-- Temporary exact reuse of the old node-[56] finite cap.  It is indexed by
the literal node-[55] Residual C leaf and is therefore unavailable on either
node-[54] terminal or an earlier bypass. -/
structure Node56NetCapTypedYellowInput (V : Type u) : Type (u + 3) where
  netCap : ∀ {residual : InitialResidual V}
    (active : Node55ResidualC V residual),
      (node56NetDeficiencyNumerator active : ℝ) ≤
        node56TauWindow *
            (p13RemainderVertices
              (Node21Context active.data.previous)).card +
          node56NetError active

theorem node56TauWindow_lt_quarter : node56TauWindow < (1 / 4 : ℝ) := by
  norm_num [node56TauWindow, node22SkeletonRateNumerator,
    node22WindowRateNumerator]

abbrev Node56Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    (Node54Bypass V) (Node55ResidualC V)
    (fun residual active => Node56Output (residual := residual) active)
    residual

/-- Append only the node-[56] mathematical payload to Residual C. -/
noncomputable def node56P13NetDeficiencyCap {V : Type u}
    (input : Node56NetCapTypedYellowInput V) {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node55Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node56Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
    fun _residual active =>
      {
        netCap := input.netCap active
        limitingCapStrict := node56TauWindow_lt_quarter
      }

noncomputable def runInitialThroughNode56 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (node56Input : Node56NetCapTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode55 quietBlock node48Input
    node52Input node54Input residual).mapYesStage
      (node56P13NetDeficiencyCap node56Input)

def node56LocalChecks : Nat := 0

theorem node56LocalChecks_eq_zero : node56LocalChecks = 0 := rfl

#print axioms node56TauWindow_lt_quarter
#print axioms node56P13NetDeficiencyCap
#print axioms runInitialThroughNode56

end Erdos64EG.Internal
