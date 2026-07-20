import Erdos64EG.Node32

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [33]: Branch D

Node [33] gives the literal strict-rank-loss yes constructor of node [32] its
manuscript name.  It proves no context, support, or compression statement.
Core transports the node-[20] bypass and node [32]'s complementary
full-cardinality constructor.
-/

/-- Node [33] is a branch name, not a second copy of node [32]'s proof.  The
framework decision carrier retains the exact strict rank-loss certificate. -/
abbrev Node33Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21)
    (_node31 : Node31Output node18 _bounded _node21 _low)
    (_rankDrop : Node32RankDrop node18) : Type := PUnit

/-- Node [33] is the selected yes continuation of node [32]. -/
abbrev Node33Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data rankDrop => Node33Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current rankDrop)
    residual

/-- Framework-owned `[32] --yes--> [33]` continuation. -/
noncomputable def node33P13RankReducingBranch {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node32Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node33Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    fun _ _data _rankDrop => PUnit.unit

noncomputable def runInitialThroughNode33 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode32 residual).mapYesStage
    node33P13RankReducingBranch

def node33LocalChecks : Nat := 0

theorem node33LocalChecks_eq_zero : node33LocalChecks = 0 := rfl

#print axioms node33P13RankReducingBranch
#print axioms runInitialThroughNode33

end Erdos64EG.Internal
