import Erdos64EG.Node163

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.FiniteSameInterfaceExchange

universe u

/-!
# Diagram node [164]: ledger retrieval of finite same-interface completeness

Node [164] consumes the node-[163] good-terminal ledger.  It does not rebuild
the CT3 run, recopy predecessor data, or introduce a graph-specific handoff:
the framework continuation retrieves exactly the `FiniteSameInterfaceExchange`
target-completeness certificate registered by node [163] for each scheduled
entry.
-/

abbrev Node164FiniteSameInterfaceOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_allGood : Node160AllCompressionOrKnown active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
      ∃ candidate : Node159Candidate active.data entry,
        FiniteSameInterfaceExchange.TargetComplete
          (node163Representatives active entry candidate)
          (node163BoundaryCompatible active entry candidate)
          (node163ResponseTable active entry candidate)

abbrev Node164Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node164FiniteSameInterfaceOutput V) residual

noncomputable def node164FiniteSameInterfaceRetrieval {V : Type u}
    {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node163Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node164Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := @Node163StrictResponseReplacementOutput V)
    (Next := @Node164FiniteSameInterfaceOutput V)
    fun _residual active _allGood node163 => by
      intro entry member
      rcases node163 entry member with
        ⟨candidate, _positive, _smaller, _sameResponse, complete⟩
      exact ⟨candidate, complete⟩

noncomputable def runInitialThroughNode164 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode163 residual).mapYesStage
    node164FiniteSameInterfaceRetrieval

def node164LocalChecks : Nat := 0

theorem node164LocalChecks_eq_zero : node164LocalChecks = 0 := rfl

#print axioms node164FiniteSameInterfaceRetrieval
#print axioms runInitialThroughNode164

end Erdos64EG.Internal
