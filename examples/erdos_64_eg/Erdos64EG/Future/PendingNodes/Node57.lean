import Erdos64EG.Future.PendingNodes.Node56
import StructuralExhaustion.Core.FocusedActiveContinuation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [57]: large-budget net cap

Node [57] is the Part-V specialization of node [56]'s error-bearing cap to
the strict-quarter tail used by the net-charge split.  Core transports every
Part-IV terminal bypass and the exact Residual C leaf.  The old verified
strict-quarter output is temporarily accepted through one typed input indexed
by that literal node-[56] leaf while its asymptotic-family producer is ported.
-/

/-- Node [57]'s sole new mathematical payload: the denominator-free exact
strict-quarter inequality used by the local charge ledger. -/
structure Node57Output {V : Type u} {residual : InitialResidual V}
    (active : Node55ResidualC V residual) : Type (u + 2) where
  strictQuarter :
    4 * node56NetDeficiencyNumerator active <
      (p13RemainderVertices
        (Node21Context active.data.previous)).card

/-- Exact temporary reuse of the old node-[57] strict-quarter result.  Both
the Residual C data and the literal node-[56] output index the assumption, so
it cannot be consumed on a Part-IV bypass or sibling branch. -/
structure Node57StrictQuarterTypedYellowInput (V : Type u) : Type (u + 3) where
  strictQuarter : ∀ {residual : InitialResidual V}
    (active : Node55ResidualC V residual)
    (node56 : Node56Output (residual := residual) active),
      4 * node56NetDeficiencyNumerator active <
        (p13RemainderVertices
          (Node21Context active.data.previous)).card

abbrev Node57Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    (Node54Bypass V) (Node55ResidualC V)
    (fun residual active => Node57Output (residual := residual) active)
    residual

/-- Append only node [57]'s strict-quarter fact on the literal node-[56]
active leaf. -/
noncomputable def node57P13LargeBudgetNetCap {V : Type u}
    (input : Node57StrictQuarterTypedYellowInput V) {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node56Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node57Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchActiveContinuation
    fun _residual active node56 =>
      ⟨input.strictQuarter active node56⟩

noncomputable def runInitialThroughNode57 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (node56Input : Node56NetCapTypedYellowInput V)
    (node57Input : Node57StrictQuarterTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode56 quietBlock node48Input
    node52Input node54Input node56Input residual).mapYesStage
      (node57P13LargeBudgetNetCap node57Input)

def node57LocalChecks : Nat := 0

theorem node57LocalChecks_eq_zero : node57LocalChecks = 0 := rfl

#print axioms node57P13LargeBudgetNetCap
#print axioms runInitialThroughNode57

end Erdos64EG.Internal
