import Erdos64EG.Future.PendingNodes.Node58

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [59]: is the global net charge nonnegative?

This is exactly the two-way diamond printed in Part V.  Core bundles the
literal node-[58] active continuation and constructs the exhaustive ordered
split.  The yes leaf goes only to node [60], and the strict-negative no leaf
goes only to node [61].
-/

abbrev Node59Active {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchActiveData
    (@Node58Active V)
    (fun residual active => Node58Output (residual := residual) active)
    residual

/-- Yes edge `[59] --yes--> [60]`. -/
abbrev Node59Nonnegative {V : Type u} (residual : InitialResidual V)
    (active : Node59Active residual) : Prop :=
  0 ≤ active.output.netCharge

/-- No edge `[59] --no--> [61]`, the strict complement over `ℝ`. -/
abbrev Node59Negative {V : Type u} (residual : InitialResidual V)
    (active : Node59Active residual) : Prop :=
  active.output.netCharge < 0

abbrev Node59Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node54Bypass V) (@Node59Active V)
    (@Node59Nonnegative V) (@Node59Negative V) residual

/-- Framework-owned exhaustive sign decision on the exact node-[58] charge. -/
noncomputable def node59P13NetChargeDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node58Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node59Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchActiveContinuation
    (fun _residual _active _node58 =>
      Classical.propDecidable (0 ≤ _node58.netCharge))
    (fun _residual _active node58 absent =>
      lt_of_not_ge absent)

noncomputable def runInitialThroughNode59 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (node56Input : Node56NetCapTypedYellowInput V)
    (node57Input : Node57StrictQuarterTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode58 quietBlock node48Input
    node52Input node54Input node56Input node57Input residual).mapYesStage
      node59P13NetChargeDecision

def node59LocalChecks : Nat := 0

theorem node59LocalChecks_eq_zero : node59LocalChecks = 0 := rfl

#print axioms node59P13NetChargeDecision
#print axioms runInitialThroughNode59

end Erdos64EG.Internal
