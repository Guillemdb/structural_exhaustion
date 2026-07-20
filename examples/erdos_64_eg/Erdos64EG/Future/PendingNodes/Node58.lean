import Erdos64EG.Future.PendingNodes.Node57

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [58]: net charge

Node [58] introduces exactly the paper's net-charge value on the literal
node-[57] large-budget leaf.  Core retains node [57]'s strict-quarter output
inside the active branch data and appends only the new charge definition.
-/

abbrev Node58Active {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchActiveData
    (Node55ResidualC V)
    (fun residual active => Node57Output (residual := residual) active)
    residual

/-- The manuscript's global net charge
`N(R) = def+(R) - sigma(R) - |R|/4`. -/
noncomputable def node58NetCharge {V : Type u}
    {residual : InitialResidual V} (active : Node58Active residual) : ℝ :=
  (node56NetDeficiencyNumerator active.data : ℝ) -
    (p13RemainderVertices
      (Node21Context active.data.data.previous)).card / 4

/-- Node [58]'s sole new payload retains the exact charge value rather than a
detached sign or branch conclusion. -/
structure Node58Output {V : Type u} {residual : InitialResidual V}
    (active : Node58Active residual) : Type (u + 2) where
  netCharge : ℝ
  netChargeExact : netCharge = node58NetCharge active

abbrev Node58Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    (Node54Bypass V) (@Node58Active V)
    (fun residual active => Node58Output (residual := residual) active)
    residual

/-- Define the charge on the exact node-[57] continuation.  No sign is
decided at this node. -/
noncomputable def node58P13NetCharge {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node57Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node58Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchActiveAgain
    fun _residual active node57 =>
      {
        netCharge := node58NetCharge ⟨active, node57⟩
        netChargeExact := rfl
      }

noncomputable def runInitialThroughNode58 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (node56Input : Node56NetCapTypedYellowInput V)
    (node57Input : Node57StrictQuarterTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode57 quietBlock node48Input
    node52Input node54Input node56Input node57Input residual).mapYesStage
      node58P13NetCharge

def node58LocalChecks : Nat := 0

theorem node58LocalChecks_eq_zero : node58LocalChecks = 0 := rfl

#print axioms node58P13NetCharge
#print axioms runInitialThroughNode58

end Erdos64EG.Internal
