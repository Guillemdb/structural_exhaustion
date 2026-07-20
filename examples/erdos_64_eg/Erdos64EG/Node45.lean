import Erdos64EG.Node44

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [45]: target / replacement / global-profile barrier

The node-[35] circuit carries an already admitted functional CT15 quotient.
On node [41]'s whole constructor, admission's represented-reduction clause
rules out every non-injective code by the certified smaller closed
representative/minimality theorem.  Hence the quotient is injective on the raw
curvature labels.  Node [46], not this node, combines that barrier with the
retained distinct collision to close the rank-drop branch.
-/

/-- Node [45]'s sole new conclusion. -/
structure Node45Output {V : Type u} {residual : InitialResidual V}
    (active : Node41Active V residual) (_whole : Node41Whole active) :
    Type (u + 3) where
  exactRawLabels : Function.Injective
    active.data.output.circuit.candidate.quotientCode

abbrev Node45Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node41Bypass V) (Node41Active V)
    (fun _ active => Node41Proper active)
    (fun _ active => Node41Whole active)
    (fun _ active whole => Node45Output active whole) residual

private noncomputable def node45Output {V : Type u}
    {residual : InitialResidual V} (active : Node41Active V residual)
    (whole : Node41Whole active) (node44 : Node44Output active whole) :
    Node45Output active whole := by
  cases node44 with
  | mk _repairIdentity =>
      exact {
        exactRawLabels :=
          Graph.SupportStratifiedDetermination.Candidate.code_injective_of_carrier_whole
            p13CurvatureSupport active.data.output.circuit.candidate whole
      }

/-- Framework-owned successor of node [44]'s exact whole-support leaf. -/
noncomputable def node45P13GlobalProfileBarrier {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node44Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node45Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (fun _ active whole node44 => node45Output active whole node44)

noncomputable def runInitialThroughNode45 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode44 residual).mapYesStage
    node45P13GlobalProfileBarrier

def node45LocalChecks : Nat := 0

theorem node45LocalChecks_eq_zero : node45LocalChecks = 0 := rfl

#print axioms node45P13GlobalProfileBarrier
#print axioms runInitialThroughNode45

end Erdos64EG.Internal
