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

theorem node147CollisionCoefficientGap {V : Type u}
    {residual : InitialResidual V} {active : Node146Active V residual}
    (node146 : Node146To147 active) :
    node146Route8Tau (node146PackingTheta (Node21Context active.previous)) <
      12 * ((1 : ℚ) / 4 -
        node146Route8Tau (node146PackingTheta
          (Node21Context active.previous))) := by
  linarith [node146.tau_lt]

theorem node147CollisionMargin_pos {V : Type u}
    {residual : InitialResidual V} {active : Node146Active V residual}
    (node146 : Node146To147 active) :
    0 < 3 - 13 *
      node146Route8Tau (node146PackingTheta
        (Node21Context active.previous)) := by
  linarith [node146.tau_lt]

/-- Exact checked residual at node `[147]`.

The two arithmetic fields are proved from the predecessor payload.  The
terminal private-carrier collision is deliberately not asserted here: it
requires the separate checked carrier ledger/no-go package from the route-8
branch. -/
structure Node147Residual {V : Type u} {residual : InitialResidual V}
    (active : Node146Active V residual) (_node146 : Node146To147 active) :
    Type (u + 3) where
  coefficientGap :
    node146Route8Tau (node146PackingTheta (Node21Context active.previous)) <
      12 * ((1 : ℚ) / 4 -
        node146Route8Tau (node146PackingTheta
          (Node21Context active.previous)))
  marginPositive :
    0 < 3 - 13 *
      node146Route8Tau (node146PackingTheta
        (Node21Context active.previous))

abbrev Node147ResidualStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V)
    (fun _residual active below =>
      Node147Residual active (Node146To147.mk below
        ((node146Route8BelowThreshold_iff_theta
          (Node21Context active.previous)).mp below)
        (node146Route8_denominator_pos_of_below
          (Node21Context active.previous) below)
        ((node146Route8Tau_lt_three_thirteenths_iff
          (node146PackingTheta (Node21Context active.previous))
          (node146Route8_denominator_pos_of_below
            (Node21Context active.previous) below)).2
          ((node146Route8BelowThreshold_iff_theta
            (Node21Context active.previous)).mp below)))) residual

noncomputable def node147Route8ResidualRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node146Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node147ResidualStage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    fun _residual _active _below node146 =>
      {
        coefficientGap := node147CollisionCoefficientGap node146
        marginPositive := node147CollisionMargin_pos node146
      }

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
