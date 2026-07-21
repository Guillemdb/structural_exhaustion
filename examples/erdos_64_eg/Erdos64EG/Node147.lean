import Erdos64EG.Node146

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [147]: route-8 private-carrier residual

Node [146]'s yes edge supplies the exact route-8 density threshold.  The
manuscript then closes by a separate route-8 private-carrier collision.  That
terminal collision is not yet present as checked Lean evidence in the direct
node chain, so this node records the complete arithmetic prefix and leaves the
carrier collision as the explicit residual to be consumed by a later checked
CT4/CT7/CT16 carrier package.
-/

theorem node147Route8Tau_lt {V : Type u}
    {residual : InitialResidual V} {active : Node146Active V residual}
    (below : Node146Route8BelowThreshold active) :
    node146Route8Tau (node146PackingTheta (Node21Context active.previous)) <
      (3 : ℚ) / 13 := by
  exact (node146Route8Tau_lt_three_thirteenths_iff
    (node146PackingTheta (Node21Context active.previous))
    (node146Route8_denominator_pos_of_below
      (Node21Context active.previous) below)).2
    ((node146Route8BelowThreshold_iff_theta
      (Node21Context active.previous)).mp below)

theorem node147CollisionCoefficientGap {V : Type u}
    {residual : InitialResidual V} {active : Node146Active V residual}
    (below : Node146Route8BelowThreshold active) :
    node146Route8Tau (node146PackingTheta (Node21Context active.previous)) <
      12 * ((1 : ℚ) / 4 -
        node146Route8Tau (node146PackingTheta
          (Node21Context active.previous))) := by
  linarith [node147Route8Tau_lt (active := active) below]

theorem node147CollisionMargin_pos {V : Type u}
    {residual : InitialResidual V} {active : Node146Active V residual}
    (below : Node146Route8BelowThreshold active) :
    0 < 3 - 13 *
      node146Route8Tau (node146PackingTheta
        (Node21Context active.previous)) := by
  linarith [node147Route8Tau_lt (active := active) below]

abbrev Node147ResidualStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V)
    (fun _residual _active _below => PUnit) residual

noncomputable def node147Route8ResidualRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node146Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node147ResidualStage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := fun _residual _active _below => PUnit)
    (Next := fun _residual _active _below => PUnit)
    fun _residual _active _below _node146 => PUnit.unit

noncomputable def runInitialThroughNode147Residual {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode146 residual).mapYesStage
    node147Route8ResidualRefinement

def node147ResidualLocalChecks : Nat := 0

theorem node147ResidualLocalChecks_eq_zero :
    node147ResidualLocalChecks = 0 := rfl

#print axioms node147Route8ResidualRefinement
#print axioms runInitialThroughNode147Residual

end Erdos64EG.Internal
