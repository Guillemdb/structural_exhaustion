import Erdos64EG.Node59

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [60]: net-cap contradiction

Node [60] closes exactly the yes edge of node [59].  Node [57] already proved
the strict negative quarter-scaled net charge on every live node-[56] leaf, and
node [58] only named that integer.  The application supplies the local
contradiction; Core owns elimination of the yes constructor and preservation of
the no constructor for node [61].
-/

/-- The complete carrier after node [60]: node-[59]'s yes leaf is terminal,
and Core retains only the literal no leaf. -/
abbrev Node60Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionYesClosed
    (@Node58Stage V) (@Node59Nonnegative V) (@Node59Negative V) residual

/-- Framework-owned closure `[59] yes -> [60]`. -/
noncomputable def node60P13NetCapContradiction {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node59Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node60Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes
    (fun _residual node58 nonnegative => by
      cases node58 with
      | mk node57 node58Output =>
          cases node57 with
          | mk node56 node57Output =>
              cases node56 with
              | bypass _ =>
                  simp [Node59Nonnegative] at nonnegative
              | degraded _data _node56 =>
                  have strict := node57Output.strictNetChargeQuarter
                  change 0 ≤ node58Output.netChargeQuarter at nonnegative
                  rw [node58Output.netChargeQuarterExact] at nonnegative
                  exact (Int.not_lt_of_ge nonnegative) strict
              | alternate _data _low _node56 =>
                  have strict := node57Output.strictNetChargeQuarter
                  change 0 ≤ node58Output.netChargeQuarter at nonnegative
                  rw [node58Output.netChargeQuarterExact] at nonnegative
                  exact (Int.not_lt_of_ge nonnegative) strict)

noncomputable def runInitialThroughNode60 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode59 residual).mapYesStage
    node60P13NetCapContradiction

def node60LocalChecks : Nat := 0

theorem node60LocalChecks_eq_zero : node60LocalChecks = 0 := rfl

end Erdos64EG.Internal
