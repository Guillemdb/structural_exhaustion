import Erdos64EG.Node33

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [34]: Residual B

Node [34] names only the literal no constructor of node [32].  It neither
charges curvature nor enters Part III.  Its branch-local payload is exactly
the full declared-coordinate equality supplied by CT15's node-[32] decision.
-/

/-- Node [34] is a branch name, not a second copy of node [32]'s proof. -/
abbrev Node34Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21)
    (_node31 : Node31Output node18 _bounded _node21 _low)
    (_fullRank : Node32FullRank node18) : Type := PUnit

/-- Node [34] is the selected no continuation of the same node-[32]
decision.  The already accumulated node-[33] stage is not consumed or rebuilt. -/
abbrev Node34Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data fullRank => Node34Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current fullRank)
    residual

/-- Framework-owned `[32] --no--> [34]` continuation. -/
noncomputable def node34P13FullRankResidual {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node32Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node34Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    fun _ _data _fullRank => PUnit.unit

/-- Both node-[33] and node-[34] are appended from the one state containing
node [32].  Node [34] retrieves node [32] directly, while Core preserves the
already accumulated node-[33] continuation. -/
noncomputable def runInitialThroughNode34 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode33 residual).mapYesStage
    node34P13FullRankResidual

def node34LocalChecks : Nat := 0

theorem node34LocalChecks_eq_zero : node34LocalChecks = 0 := rfl

#print axioms node34P13FullRankResidual
#print axioms runInitialThroughNode34

end Erdos64EG.Internal
