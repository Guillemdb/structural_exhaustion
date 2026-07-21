import Erdos64EG.Node39

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [40]: enlarged connected determination support

Node [40] is the literal no continuation of node [38].  Its active constructor
retains exactly the same node-[35] determination certificate, node [36]'s
original-interface universality proof, and node [38]'s strict support-growth
proof.  Consequently its carrier is the connected support `Z ⊋ C` from the
paper, with the certificate's determination and inclusion-minimality fields
still available in the one accumulated ledger.  No new support, handoff, or
application-owned record is constructed here.
-/

/-- The framework-owned active cursor whose final-no constructor is precisely
the connected enlarged-support residual printed at node [40]. -/
abbrev Node40Stage {V : Type u} (residual : InitialResidual V) :=
  (node35FocusedFamily V).FinalNoActive
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node37TargetDefect data.output)
    (fun _ data _ => Node38AtOriginal data.output)
    (fun _ data _ => Node38Enlarged data.output) residual

/-- Framework-owned `[38] --no--> [40]` continuation.  The sibling node-[39]
closure is accumulated independently and is not an input to this edge. -/
noncomputable def node40P13EnlargedConnectedSupport {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node38Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node40Stage V) :=
  Core.ResidualRefinement.State.StageNode.focusFocusedYesContinuationFinalNo
    (node35FocusedFamily V)

noncomputable def runInitialThroughNode40 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode38 residual).mapYesStage
    node40P13EnlargedConnectedSupport

def node40LocalChecks : Nat := 0

theorem node40LocalChecks_eq_zero : node40LocalChecks = 0 := rfl

#print axioms node40P13EnlargedConnectedSupport
#print axioms runInitialThroughNode40

end Erdos64EG.Internal
