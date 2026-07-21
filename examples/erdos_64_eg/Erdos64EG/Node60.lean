import Erdos64EG.Node59
import StructuralExhaustion.Core.StrictGapAbsorption

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [60]: net-cap contradiction

Node [60] closes exactly the yes edge of node [59].  Node [56] already
produced the strict quarter bound on the same remainder after the paper's
large-enough tail absorbed the inherited `o(|R|)` term.  Node [58] named the
signed net charge.  This node only compares those two framework-carried facts
and lets Core remove the closed yes constructor.
-/

/-- Node [60]'s branch-local contradiction. -/
theorem node60_netCapContradiction {V : Type u} {residual : InitialResidual V}
    (node58 : Node58Stage residual)
    (nonnegative : Node59Nonnegative node58) : False := by
  cases node58 with
  | mk node57 node58Output =>
      cases node57 with
      | mk node56 node57Output =>
          cases node56 with
          | bypass _ =>
              simp [Node59Nonnegative] at nonnegative
          | degraded data node56Output =>
              change 0 ≤ node58Output.remainderNetChargeQuarter at nonnegative
              rw [node58Output.remainderNetChargeQuarterExact] at nonnegative
              exact
                StructuralExhaustion.Core.StrictGapAbsorption.signed_nonnegative_false_of_nat_sub_quarter_negative
                  (a := (p13RemainderCurvatureProfile
                    (Node21Context data.data.previous)).positiveDeficiency)
                  (b := Graph.InducedPathWindowLedger.remainderSurplus
                    (Node21Context data.data.previous).G.object)
                  (scale := (p13RemainderVertices
                    (Node21Context data.data.previous)).card)
                  (by
                    simpa [node56RemainderNetDeficiencyNumerator] using
                      node56Output.remainderNetChargeQuarterNegative)
                  nonnegative
          | alternate data _low node56Output =>
              change 0 ≤ node58Output.remainderNetChargeQuarter at nonnegative
              rw [node58Output.remainderNetChargeQuarterExact] at nonnegative
              exact
                StructuralExhaustion.Core.StrictGapAbsorption.signed_nonnegative_false_of_nat_sub_quarter_negative
                  (a := (p13RemainderCurvatureProfile
                    (Node21Context data.data.previous)).positiveDeficiency)
                  (b := Graph.InducedPathWindowLedger.remainderSurplus
                    (Node21Context data.data.previous).G.object)
                  (scale := (p13RemainderVertices
                    (Node21Context data.data.previous)).card)
                  (by
                    simpa [node56RemainderNetDeficiencyNumerator] using
                      node56Output.remainderNetChargeQuarterNegative)
                  nonnegative

/-- The complete carrier after node [60]: the node-[59] nonnegative edge is
terminally closed, and Core retains only the literal negative edge for node
[61]. -/
abbrev Node60Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionYesClosed
    (@Node58Stage V) (@Node59Nonnegative V) (@Node59Negative V) residual

/-- Framework-owned node-[60] closure. -/
noncomputable def node60P13NetCapContradiction {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node59Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node60Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes
    (fun _residual node58 nonnegative =>
      node60_netCapContradiction node58 nonnegative)

noncomputable def runInitialThroughNode60 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode59 residual).mapYesStage
    node60P13NetCapContradiction

def node60LocalChecks : Nat := 0

theorem node60LocalChecks_eq_zero : node60LocalChecks = 0 := rfl

end Erdos64EG.Internal
