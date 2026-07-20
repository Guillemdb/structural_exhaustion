import Erdos64EG.Node42

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [43]: whole-graph delocalization

Node [43] is the literal no continuation of node [41].  It transports the
whole tag from the admitted CT15 candidate carrier to the exact determination
carrier retained by node [35], using only the previously proved carrier
equality.  Node [42]'s proper closure is accumulated in the same ledger but is
not a mathematical predecessor of this edge.
-/

/-- The one new bridge at node [43]: the determination support `Z` itself is
the whole graph, not merely the equal CT15 candidate carrier. -/
structure Node43Output {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) (_whole : Node41Whole active) :
    Type (u + 3) where
  certificateCarrierWhole : active.data.output.certificate.carrier.IsWhole

abbrev Node43Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active)
    (fun _ active whole => Node43Output active whole) residual

private def node43Output {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) (whole : Node41Whole active) :
    Node43Output active whole where
  certificateCarrierWhole :=
    active.data.output.supportCertificate.carrierExact.symm ▸ whole

/-- Framework-owned `[41] --no--> [43]` continuation. -/
noncomputable def node43P13WholeGraphDelocalization {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node41Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node43Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (fun _ active whole => node43Output active whole)

noncomputable def runInitialThroughNode43 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode42 residual).mapYesStage
    node43P13WholeGraphDelocalization

def node43LocalChecks : Nat := 0

theorem node43LocalChecks_eq_zero : node43LocalChecks = 0 := rfl

#print axioms node43P13WholeGraphDelocalization
#print axioms runInitialThroughNode43

end Erdos64EG.Internal
