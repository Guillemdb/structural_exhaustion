import Erdos64EG.Node43
import StructuralExhaustion.Graph.OneThreeRepair

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [44]: the 1--3 repair identity

On node [43]'s exact whole-support continuation, every delayed compensation
component satisfying the paper's finite 1--3 component hypotheses obeys the
handshake/cycle-rank identity

`s = p - 2 + 2 * beta - sigma`.

The graph layer computes all five quantities from one supplied component and
proves the identity symbolically.  No component family or graph universe is
enumerated.
-/

/-- Only the paper-local arithmetic theorem first attached at node [44]. -/
structure Node44Output {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) (_whole : Node41Whole active) :
    Type (u + 3) where
  repairIdentity : ∀ (component : Graph.OneThreeRepair.Component
      (P13RemainderVertex (Node21Context active.data.data.previous))),
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank - component.surplus

abbrev Node44Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active)
    (fun _ active whole => Node44Output active whole) residual

private noncomputable def node44Output {V : Type u}
    {residual : InitialResidual V} (active : Node41Active V residual)
    (whole : Node41Whole active) (_node43 : Node43Output active whole) :
    Node44Output active whole where
  repairIdentity := fun component => component.identity

/-- Framework-owned successor of the exact node-[43] no continuation. -/
noncomputable def node44P13RepairIdentity {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node43Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node44Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (fun _ active whole node43 => node44Output active whole node43)

noncomputable def runInitialThroughNode44 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode43 residual).mapYesStage
    node44P13RepairIdentity

def node44LocalChecks : Nat := 0

theorem node44LocalChecks_eq_zero : node44LocalChecks = 0 := rfl

#print axioms node44P13RepairIdentity
#print axioms runInitialThroughNode44

end Erdos64EG.Internal
