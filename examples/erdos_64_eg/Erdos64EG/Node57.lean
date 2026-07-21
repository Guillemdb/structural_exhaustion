import Erdos64EG.Node56

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [57]: large-budget net cap

Node [57] consumes the literal node-[56] merged residual and performs only the
paper-local arithmetic handoff: it exposes the denominator-free manuscript
net-charge numerator `4 * (def⁺(R) - σ_R) - |R|` on the same remainder.
The finite total-surplus strict inequality is retained only as the compiled
node-[60] terminal certificate; it is not the node-[61] support-localization
object.  Core owns the stage transport through `mapStage`.
-/

/-- Node [57]'s sole payload: the large-budget net cap on the same residual.
This is the Part-V handoff form of node [56]'s exact finite cap. -/
structure Node57Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_node56 : Node56Output active) : Type (u + 2) where
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
  tauWin_lt_quarter : node56TauWin < (1 / 4 : ℝ)
  remainderNetDeficiencyRealCap :
    (node56RemainderNetDeficiencyNumerator
      (Node21Context active.previous) : ℝ) ≤
      node56TauWin *
          (p13RemainderVertices
            (Node21Context active.previous)).card +
        Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context active.previous).G.object
  /-- The paper's exact Part-V numerator:
  `4 * (def⁺(R) - σ_R) - |R|`. -/
  remainderNetChargeQuarter : Int
  remainderNetChargeQuarterExact :
    remainderNetChargeQuarter =
      4 * (((p13RemainderCurvatureProfile
            (Node21Context active.previous)).positiveDeficiency : Int) -
          (Graph.InducedPathWindowLedger.remainderSurplus
            (Node21Context active.previous).G.object : Int)) -
        ((p13RemainderVertices
          (Node21Context active.previous)).card : Int)
  /-- Finite node-[60] contradiction numerator:
  `4 * (def⁺(R) - σ(G)) - |R|`.  This is not the node-[61] object. -/
  strictNetChargeQuarter :
    4 * (((p13RemainderCurvatureProfile
          (Node21Context active.previous)).positiveDeficiency : Int) -
        (Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context active.previous).G.object : Int)) -
      ((p13RemainderVertices
        (Node21Context active.previous)).card : Int) < 0
  localWork : 0 = 0 := rfl

/-- The complete carrier after node [57]. -/
abbrev Node57Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node56Stage V)
    (fun _residual node56 =>
      match node56 with
      | .bypass _ => PUnit
      | .degraded data output => Node57Output data.data output
      | .alternate data _ output => Node57Output data.data output)
    residual

/-- Framework-owned successor `[56] -> [57]`.  Bypass leaves are transported
by Core's dependent successor; both live leaves consume their literal
node-[56] output. -/
noncomputable def node57P13LargeBudgetNetCap {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node56Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node57Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (Previous := @Node56Stage V)
    (Next := fun _residual node56 =>
      match node56 with
      | .bypass _ => PUnit
      | .degraded data output => Node57Output data.data output
      | .alternate data _ output => Node57Output data.data output)
    fun _residual node56 =>
      match node56 with
      | .bypass _ => PUnit.unit
      | .degraded _data output =>
          let active : Node50Active V _residual := _data.data
          let ctx := Node21Context (Node50Active.previous active)
          have remainderPositive :
              0 < (p13RemainderVertices ctx).card := by
            simpa [ctx, active, Node50Active.previous] using
              _data.data.data.current.node30.remainderPositive
          have remainderPositiveReal :
              (0 : ℝ) < ((p13RemainderVertices ctx).card : ℝ) := by
            exact_mod_cast remainderPositive
          have strictReal :
              (4 : ℝ) *
                  (((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) -
                    Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) -
                ((p13RemainderVertices ctx).card : ℝ) < 0 := by
            have cap := output.netDeficiencyRealCap
            have tau := output.tauWin_lt_quarter
            change ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
                node56TauWin * (p13RemainderVertices ctx).card +
                  Graph.InducedPathWindowLedger.totalSurplus ctx.G.object at cap
            nlinarith
          { netDeficiencyFiniteCap := output.netDeficiencyFiniteCap
            tauWin_lt_quarter := output.tauWin_lt_quarter
            remainderNetDeficiencyRealCap := by
              simpa [ctx, Node50Active.previous] using
                output.remainderNetDeficiencyRealCap
            remainderNetChargeQuarter :=
              4 * (((p13RemainderCurvatureProfile ctx).positiveDeficiency : Int) -
                  (Graph.InducedPathWindowLedger.remainderSurplus
                    ctx.G.object : Int)) -
                ((p13RemainderVertices ctx).card : Int)
            remainderNetChargeQuarterExact := by
              rfl
            strictNetChargeQuarter := by
              exact_mod_cast strictReal
            localWork := rfl }
      | .alternate _data _ output =>
          let active : Node50Active V _residual := _data.data
          let ctx := Node21Context (Node50Active.previous active)
          have remainderPositive :
              0 < (p13RemainderVertices ctx).card := by
            simpa [ctx, active, Node50Active.previous] using
              _data.data.data.current.node30.remainderPositive
          have remainderPositiveReal :
              (0 : ℝ) < ((p13RemainderVertices ctx).card : ℝ) := by
            exact_mod_cast remainderPositive
          have strictReal :
              (4 : ℝ) *
                  (((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) -
                    Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) -
                ((p13RemainderVertices ctx).card : ℝ) < 0 := by
            have cap := output.netDeficiencyRealCap
            have tau := output.tauWin_lt_quarter
            change ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
                node56TauWin * (p13RemainderVertices ctx).card +
                  Graph.InducedPathWindowLedger.totalSurplus ctx.G.object at cap
            nlinarith
          { netDeficiencyFiniteCap := output.netDeficiencyFiniteCap
            tauWin_lt_quarter := output.tauWin_lt_quarter
            remainderNetDeficiencyRealCap := by
              simpa [ctx, Node50Active.previous] using
                output.remainderNetDeficiencyRealCap
            remainderNetChargeQuarter :=
              4 * (((p13RemainderCurvatureProfile ctx).positiveDeficiency : Int) -
                  (Graph.InducedPathWindowLedger.remainderSurplus
                    ctx.G.object : Int)) -
                ((p13RemainderVertices ctx).card : Int)
            remainderNetChargeQuarterExact := by
              rfl
            strictNetChargeQuarter := by
              exact_mod_cast strictReal
            localWork := rfl }

noncomputable def runInitialThroughNode57 {V : Type u}
    (_residual : InitialResidual V) :=
  (runInitialThroughNode56 _residual).mapYesStage
    node57P13LargeBudgetNetCap

def node57LocalChecks : Nat := 0

theorem node57LocalChecks_eq_zero : node57LocalChecks = 0 := rfl

end Erdos64EG.Internal
