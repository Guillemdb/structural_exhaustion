import Erdos64EG.Node38

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [39]: proper-atom compression

Only node [38]'s literal at-original constructor enters this terminal.  It
transports the certificate's stored representative to the original proper
atom, then invokes the graph-owned CT3/minimality closure.  The enlarged
sibling is untouched.
-/

/-- Node [39] closes only the at-original leaf of node [38]. -/
abbrev Node39Stage {V : Type u} (residual : InitialResidual V) :=
  (node35FocusedFamily V).FinalYesClosed
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node37TargetDefect data.output)
    (fun _ data _ => Node38AtOriginal data.output)
    (fun _ data _ => Node38Enlarged data.output) residual

/-- Framework-owned `[38] --yes--> [39]` closure.  The only application
mathematics is the existing graph CT3 representative contradiction. -/
noncomputable def node39P13ProperAtomCompression {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node38Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node39Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedYesContinuationFinalYes
    (node35FocusedFamily V)
    (fun _ data _ equal =>
      Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
        data.output.certificate.original_eligible
        (data.output.certificate.originalRepresentative equal))

noncomputable def runInitialThroughNode39 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode38 residual).mapYesStage
    node39P13ProperAtomCompression

def node39LocalChecks : Nat := 0

theorem node39LocalChecks_eq_zero : node39LocalChecks = 0 := rfl

#print axioms node39P13ProperAtomCompression
#print axioms runInitialThroughNode39

end Erdos64EG.Internal
