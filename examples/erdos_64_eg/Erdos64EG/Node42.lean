import Erdos64EG.Node41

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [42]: proper-support smearing closure

The node-[41] proper constructor is already on the final context-universal
carrier of the admitted CT15 quotient.  Admission therefore supplies its
literal represented reduction, and the graph-owned CT3/minimality theorem
makes that non-injective proper-carrier proposal impossible.  Node [42] closes
only this constructor; the whole constructor remains available independently
to node [43].
-/

abbrev Node42Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active) residual

/-- The proper-carrier branch contradicts the distinct collision retained by
the exact CT15 circuit.  `injective_of_originalEligible` consumes the stored
CT3 representative; no replacement or context is reconstructed here. -/
theorem node42ProperSupportImpossible {V : Type u}
    {residual : InitialResidual V} (active : Node41Active V residual)
    (proper : Node41Proper active) : False := by
  let output := active.data.output
  have certificateProper : output.certificate.carrier.OriginalEligible :=
    output.supportCertificate.carrierExact.symm ▸ proper
  exact Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
    certificateProper output.certificate.representative

/-- Framework-owned closure of `[41] --yes--> [42]`. -/
noncomputable def node42P13ProperSupportSmearingClosure {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node41Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node42Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
    (fun _ active proper => node42ProperSupportImpossible active proper)

noncomputable def runInitialThroughNode42 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode41 residual).mapYesStage
    node42P13ProperSupportSmearingClosure

def node42LocalChecks : Nat := 0

theorem node42LocalChecks_eq_zero : node42LocalChecks = 0 := rfl

#print axioms node42ProperSupportImpossible
#print axioms node42P13ProperSupportSmearingClosure
#print axioms runInitialThroughNode42

end Erdos64EG.Internal
