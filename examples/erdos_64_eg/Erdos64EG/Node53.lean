import Erdos64EG.Node52

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [53]: remaining non-curvature budget

Node [53] is the second paper dichotomy, executed only on node [50]'s literal
low-entropy constructor.  Its two constructors are exactly the natural-power
comparison printed in the paper.  Core retains node [52]'s completed high
leaf, every earlier bypass, the exact low constructor, and the full
accumulated ledger.
-/

/-- The exact forced curvature power `A=543958^r`. -/
noncomputable def node53ForcedPower {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  543958 ^ (p13CurvatureCoordinates (Node21Context active.previous)).card

/-- The exact flat comparison power `B=111286^r`. -/
noncomputable def node53FlatPower {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  111286 ^ (p13CurvatureCoordinates (Node21Context active.previous)).card

/-- The strict low-entropy allowance `U=n^|R|` inherited from node [50]. -/
noncomputable def node53UpperPower {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  (Node21Context active.previous).G.object.input.vertices.card ^
    (p13RemainderVertices (Node21Context active.previous)).card

/-- Yes edge `[53] -> [54]`. -/
abbrev Node53Small {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual)
    (_low : Node50Low residual active) : Prop :=
  node53FlatPower active ^ 10 * node53UpperPower active ≤
    node53ForcedPower active ^ 10

/-- No edge `[53] -> [55]`. -/
abbrev Node53Large {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual)
    (_low : Node50Low residual active) : Prop :=
  node53ForcedPower active ^ 10 <
    node53FlatPower active ^ 10 * node53UpperPower active

/-- Exact Part-IV carrier after the node-[53] diamond. -/
abbrev Node53Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchYesContinuationNoDecision
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (@Node53Small V) (@Node53Large V) residual

/-- Framework-owned exhaustive decision on node [50]'s exact low leaf. -/
noncomputable def node53P13RemainingBudgetDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node52Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node53Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
      (fun _residual active low => Classical.propDecidable
        (Node53Small _ active low))
      (fun _residual _active _low absent => Nat.lt_of_not_ge absent)

noncomputable def runInitialThroughNode53 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode52 residual).mapYesStage
    node53P13RemainingBudgetDecision

/-- One proof-level ordered comparison and no finite local scan. -/
def node53LocalChecks : Nat := 0

theorem node53LocalChecks_eq_zero : node53LocalChecks = 0 := rfl

#print axioms node53P13RemainingBudgetDecision
#print axioms runInitialThroughNode53

end Erdos64EG.Internal
