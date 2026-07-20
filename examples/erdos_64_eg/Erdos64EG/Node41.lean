import Erdos64EG.Node40

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [41]: proper or whole enlarged carrier

Node [40]'s focused active leaf is the inclusion-minimal connected support
`Z ⊋ C`.  Node [41] reads only the proper/whole tag already stored by the
graph support interface and makes the paper's exhaustive decision.  The
framework keeps every unrelated terminal leaf in an opaque bypass and retains
the exact active node-[40] payload on both constructors.
-/

/-- Framework-owned bypass type of node [40].  It is named only to instantiate
the generic focused-decision API; Erdős code never inspects it. -/
abbrev Node41Bypass (V : Type u) :=
  (node35FocusedFamily V).FinalNoBypass
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node37TargetDefect data.output)
    (fun _ data _ => Node38AtOriginal data.output)
    (fun _ data _ => Node38Enlarged data.output)

/-- The exact active node-[40] leaf packaged by Core. -/
abbrev Node41Active (V : Type u) :=
  (node35FocusedFamily V).FinalNoData
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data _ => Node38Enlarged data.output)

/-- The yes edge printed at node [41].  The CT15 candidate carrier is the
same carrier `Z` selected by node [35]'s exact support certificate. -/
abbrev Node41Proper {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) : Prop :=
  active.data.output.circuit.candidate.carrier.OriginalEligible

/-- The no edge printed at node [41]. -/
abbrev Node41Whole {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) : Prop :=
  active.data.output.circuit.candidate.carrier.IsWhole

abbrev Node41Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active) residual

/-- Framework-owned node-[41] diamond.  The graph layer decides the stored
scope tag without scanning a graph, support family, or context universe. -/
noncomputable def node41P13CarrierScopeDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node40Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node41Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranch
    (fun _ active =>
      active.data.output.circuit.candidate.carrier.originalEligibleDecidable)
    (fun _ active absent =>
      active.data.output.circuit.candidate.carrier
        |>.whole_of_not_originalEligible absent)

noncomputable def runInitialThroughNode41 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode40 residual).mapYesStage
    node41P13CarrierScopeDecision

def node41LocalChecks : Nat := 0

theorem node41LocalChecks_eq_zero : node41LocalChecks = 0 := rfl

#print axioms node41P13CarrierScopeDecision
#print axioms runInitialThroughNode41

end Erdos64EG.Internal
