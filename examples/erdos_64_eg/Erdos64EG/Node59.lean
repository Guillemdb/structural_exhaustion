import Erdos64EG.Node58

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [59]: nonnegative net charge?

Node [59] is exactly the Part-V yes/no split
`\mathcal N(R) \ge 0?`.  Node [58] already named the quarter-scaled net charge
on the literal incoming residual.  This file supplies only the two branch
predicates and lets Core execute the dependent decision over the exact
node-[58] stage.
-/

/-- Yes edge `[59] -> [60]`: the quarter-scaled net charge is nonnegative.
Closed/bypass leaves cannot take this paper edge. -/
def Node59Nonnegative {V : Type u} {residual : InitialResidual V}
    (node58 : Node58Stage residual) : Prop :=
  match node58 with
  | ⟨⟨.bypass _, _⟩, _⟩ => False
  | ⟨⟨.degraded _data _node56, _node57⟩, output⟩ =>
      0 ≤ output.netChargeQuarter
  | ⟨⟨.alternate _data _low _node56, _node57⟩, output⟩ =>
      0 ≤ output.netChargeQuarter

/-- No edge `[59] -> [61]`: the quarter-scaled net charge is negative.
Closed/bypass leaves are transported by Core and never create application
routing. -/
def Node59Negative {V : Type u} {residual : InitialResidual V}
    (node58 : Node58Stage residual) : Prop :=
  match node58 with
  | ⟨⟨.bypass _, _⟩, _⟩ => True
  | ⟨⟨.degraded _data _node56, _node57⟩, output⟩ =>
      output.netChargeQuarter < 0
  | ⟨⟨.alternate _data _low _node56, _node57⟩, output⟩ =>
      output.netChargeQuarter < 0

/-- The complete carrier after node [59]. -/
abbrev Node59Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecision
    (@Node58Stage V) (@Node59Nonnegative V) (@Node59Negative V) residual

/-- Framework-owned exhaustive split `[59]`: applications provide only
decidability of the paper predicate and the ordered-complement theorem. -/
noncomputable def node59P13NetChargeDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node58Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node59Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideUsingStage
    (Previous := @Node58Stage V)
    (yes := @Node59Nonnegative V)
    (no := @Node59Negative V)
    (fun _residual node58 =>
      Classical.propDecidable (Node59Nonnegative node58))
    (fun _residual node58 absent => by
      cases node58 with
      | mk node57 output =>
          cases node57 with
          | mk node56 node57Output =>
              cases node56 <;>
                simp [Node59Nonnegative, Node59Negative] at absent ⊢
              all_goals exact absent)

noncomputable def runInitialThroughNode59 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode58 residual).mapYesStage
    node59P13NetChargeDecision

def node59LocalChecks : Nat := 0

theorem node59LocalChecks_eq_zero : node59LocalChecks = 0 := rfl

end Erdos64EG.Internal
