import Erdos64EG.Node55
import StructuralExhaustion.Core.GracefulDegradation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [56]: large-budget net-deficiency cap

Node [56] consumes only node [55]'s literal Residual-C leaf.  Its quantitative
input is the finite net-deficiency cap produced at node [30] and retained
inside node [31]'s accumulated successor payload.  The node adds the paper's
normalized `τ_win` statement and the exact `τ_win < 1/4` arithmetic.
-/

/-- The exact rational coefficient printed as `τ_win`. -/
noncomputable def node56TauWin : ℝ := node30WindowDeficiencyRate

theorem node56TauWin_lt_quarter :
    node56TauWin < (1 / 4 : ℝ) := by
  norm_num [node56TauWin, node30WindowDeficiencyRate,
    node22SkeletonRateNumerator, node25RemainderRateNumerator]

/-- Only the net-cap mathematics first established at node [56]. -/
structure Node56Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Type (u + 2) where
  netDeficiencyFiniteCap :
    node25RemainderRateNumerator *
        (p13RemainderCurvatureProfile
          (Node21Context active.previous)).positiveDeficiency ≤
      15 * node22SkeletonRateNumerator *
          (p13RemainderVertices
            (Node21Context active.previous)).card +
        node25RemainderRateNumerator *
          Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context active.previous).G.object
  netDeficiencyRealCap :
    ((p13RemainderCurvatureProfile
      (Node21Context active.previous)).positiveDeficiency : ℝ) ≤
      node56TauWin *
          (p13RemainderVertices
            (Node21Context active.previous)).card +
        Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context active.previous).G.object
  tauWin_lt_quarter : node56TauWin < (1 / 4 : ℝ)
  localWork : 0 = 0 := rfl

/-- The complete carrier after the large-budget net-cap node. -/
abbrev Node56Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.GuardedDegradationMerged
    (Node50Bypass V) (Node50Active V) (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (@Node53Small V) (@Node53Large V)
    (fun residual active high node52 =>
      Node54HighTerminal (residual := residual) active high node52)
    (@Node54ProductFit V)
    (fun _residual active => Node55Output active)
    (fun _residual active => Node56Output active) residual

/-- Framework-owned successor of node [55]. -/
noncomputable def node56P13LargeBudgetNetCap {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node55Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node56Stage V) :=
  Core.ResidualRefinement.State.StageNode.mergeGuardedDegradation
    fun _residual active => by
      let node31 := active.data.current
      let node30 := node31.node30
      let ctx := Node21Context active.previous
      have finiteCap :
          node25RemainderRateNumerator *
              (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
            15 * node22SkeletonRateNumerator *
                (p13RemainderVertices ctx).card +
              node25RemainderRateNumerator *
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        simpa [ctx, node31, node30] using node30.netDeficiencyFiniteCap
      have ratePos : (0 : ℝ) < node25RemainderRateNumerator := by
        norm_num [node25RemainderRateNumerator]
      have finiteCapReal :
          (node25RemainderRateNumerator : ℝ) *
              ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
            (15 : ℝ) * node22SkeletonRateNumerator *
                ((p13RemainderVertices ctx).card : ℝ) +
              (node25RemainderRateNumerator : ℝ) *
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact_mod_cast finiteCap
      have divided :=
        div_le_div_of_nonneg_right finiteCapReal ratePos.le
      have realCap :
          ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
            node56TauWin * (p13RemainderVertices ctx).card +
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        calc
          ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) =
              ((node25RemainderRateNumerator : ℝ) *
                ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ)) /
                node25RemainderRateNumerator := by
                field_simp [ne_of_gt ratePos]
          _ ≤ ((15 : ℝ) * node22SkeletonRateNumerator *
                  ((p13RemainderVertices ctx).card : ℝ) +
                (node25RemainderRateNumerator : ℝ) *
                  Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) /
                node25RemainderRateNumerator := divided
          _ = node56TauWin * (p13RemainderVertices ctx).card +
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
                rw [node56TauWin, node30WindowDeficiencyRate]
                field_simp [ne_of_gt ratePos]
                norm_num [node22SkeletonRateNumerator]
                ring
      exact {
        netDeficiencyFiniteCap := by
          simpa [ctx] using finiteCap
        netDeficiencyRealCap := by
          simpa [ctx] using realCap
        tauWin_lt_quarter := node56TauWin_lt_quarter
        localWork := rfl
      }

noncomputable def runInitialThroughNode56 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode55 residual).mapYesStage
    node56P13LargeBudgetNetCap

def node56LocalChecks : Nat := 0

theorem node56LocalChecks_eq_zero : node56LocalChecks = 0 := rfl

#print axioms node56P13LargeBudgetNetCap
#print axioms runInitialThroughNode56

end Erdos64EG.Internal
