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

/-- Exact natural-number numerator of the manuscript remainder net deficiency
`def⁺(R)-σ_R`.  The natural subtraction is the finite representative of the
nonnegative large-budget numerator; node [58] separately names the signed
quarter-charge expression used by localization. -/
noncomputable def node56RemainderNetDeficiencyNumerator
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u}
      PackedTarget.{u}) : Nat :=
  (p13RemainderCurvatureProfile ctx).positiveDeficiency -
    Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object

/-- The exact finite upper budget for the manuscript numerator
`def⁺(R)-σ_R`, before the strict quarter comparison is applied. -/
noncomputable def node56CoverageNetBudgetUpper
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u}
      PackedTarget.{u}) : Nat :=
  15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
    Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object

/-- Current-chain form of the legacy `P13QuarterNetBudget`: the finite
strict-quarter budget on the same selected packing and remainder. -/
def Node56QuarterNetBudget {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) : Prop :=
  4 * node56CoverageNetBudgetUpper (Node21Context node18) <
    (p13RemainderVertices (Node21Context node18)).card

/-- The node-[29] surplus-adjusted incidence supply bounds the actual
`def⁺(R)-σ_R` numerator by the exact finite budget. -/
theorem node56RemainderNetDeficiencyNumerator_le_budget
    {V : Type u} {residual : InitialResidual V}
    (budgetLedger : Node29RemainderNetBudgetAvailable residual)
    (active : Node50Active V residual) :
    node56RemainderNetDeficiencyNumerator
        (Node21Context active.previous) ≤
      node56CoverageNetBudgetUpper (Node21Context active.previous) := by
  let ctx := Node21Context active.previous
  unfold node56RemainderNetDeficiencyNumerator
    node56CoverageNetBudgetUpper
  simpa [ctx, Node50Active.previous] using
    budgetLedger active.data.previous active.data.outerProof
      active.data.outerOutput active.data.innerProof

/-- The exact finite strict-quarter bridge used by nodes [57]--[60]. -/
theorem node56RemainderStrictQuarter_of_budget
    {V : Type u} {residual : InitialResidual V}
    (budgetLedger : Node29RemainderNetBudgetAvailable residual)
    (active : Node50Active V residual)
    (budget : Node56QuarterNetBudget active.previous) :
    4 * node56RemainderNetDeficiencyNumerator
        (Node21Context active.previous) <
      (p13RemainderVertices (Node21Context active.previous)).card := by
  have scaled :
      4 * node56RemainderNetDeficiencyNumerator
          (Node21Context active.previous) ≤
        4 * node56CoverageNetBudgetUpper (Node21Context active.previous) :=
    Nat.mul_le_mul_left 4
      (node56RemainderNetDeficiencyNumerator_le_budget budgetLedger active)
  exact scaled.trans_lt budget

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
  /-- The actual manuscript large-budget cap
  `(def⁺(R)-σ_R)/|R| ≤ τ_win + o(1)`, kept in finite error-bearing form. -/
  remainderNetDeficiencyRealCap :
    (node56RemainderNetDeficiencyNumerator
      (Node21Context active.previous) : ℝ) ≤
      node56TauWin *
          (p13RemainderVertices
            (Node21Context active.previous)).card +
        Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context active.previous).G.object
  /-- Conditional strict-quarter eliminator.  The producer of
  `Node56QuarterNetBudget` is a separate predecessor obligation; once present
  in the accumulated ledger, nodes [57]--[60] consume this bridge without
  reopening incidence accounting. -/
  remainderStrictQuarterOfBudget :
    Node56QuarterNetBudget active.previous →
      4 * node56RemainderNetDeficiencyNumerator
          (Node21Context active.previous) <
        (p13RemainderVertices
          (Node21Context active.previous)).card
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
      (Core.ResidualRefinement.State.Available (@Node55Stage V)) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node29Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node56Stage V) :=
  Core.ResidualRefinement.State.StageNode.mergeGuardedDegradationDerived
    (Core.ResidualRefinement.State.LedgerQuery.entailedStage
      (facts := facts) (Stage := @Node29Stage V)
      (property := @Node29RemainderNetBudgetAvailable V))
    fun _residual budgetLedger active => by
      let node31 := active.data.current
      let node30 := node31.node30
      let ctx := Node21Context active.data.previous
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
      have remainderNetRealCap :
          (node56RemainderNetDeficiencyNumerator ctx : ℝ) ≤
            node56TauWin * (p13RemainderVertices ctx).card +
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        have numeratorLe :
            node56RemainderNetDeficiencyNumerator ctx ≤
              (p13RemainderCurvatureProfile ctx).positiveDeficiency := by
          unfold node56RemainderNetDeficiencyNumerator
          exact Nat.sub_le _ _
        have numeratorLeReal :
            (node56RemainderNetDeficiencyNumerator ctx : ℝ) ≤
              ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) := by
          exact_mod_cast numeratorLe
        exact numeratorLeReal.trans realCap
      exact {
        netDeficiencyFiniteCap := by
          simpa [ctx, Node50Active.previous] using finiteCap
        netDeficiencyRealCap := by
          simpa [ctx, Node50Active.previous] using realCap
        remainderNetDeficiencyRealCap := by
          simpa [ctx, Node50Active.previous] using remainderNetRealCap
        remainderStrictQuarterOfBudget := by
          intro budget
          simpa [ctx, Node50Active.previous] using
            (node56RemainderStrictQuarter_of_budget budgetLedger active budget)
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
