import Erdos64EG.Node163

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.FiniteSameInterfaceExchange

universe u

/-!
# Diagram node [164]: ledger retrieval of finite same-interface replacement

Node [164] consumes the node-[163] good-terminal ledger.  It does not rebuild
the CT3 run, recopy predecessor data, or introduce a graph-specific handoff:
the framework continuation retrieves the complete finite same-interface
replacement package registered by node [163] for each scheduled entry.
-/

abbrev Node164FiniteSameInterfaceReplacementOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_allGood : Node160AllCompressionOrKnown active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
      ∃ candidate : Node159Candidate active.data entry,
        0 < candidate.1.1 ∧
          candidate.1.1 < node159SourceLength active.data entry ∧
          CT3.SameResponse (node159Spec active.data entry)
            candidate.1.1 (node159SourceLength active.data entry) ∧
          FiniteSameInterfaceExchange.TargetComplete
            (node163Representatives active entry candidate)
            (node163BoundaryCompatible active entry candidate)
            (node163ResponseTable active entry candidate)

abbrev Node164Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node164FiniteSameInterfaceReplacementOutput V) residual

noncomputable def node164FiniteSameInterfaceRetrieval {V : Type u}
    {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node163Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node164Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuationDerived
    (Output := @Node163StrictResponseReplacementOutput V)
    (Next := @Node164FiniteSameInterfaceReplacementOutput V)
    (Core.ResidualRefinement.State.LedgerQuery.pure
      (facts := facts) (fun _residual => ()))
    fun _residual (_unit : Unit) active _allGood node163 => by
      intro entry member
      exact node163 entry member

noncomputable def runInitialThroughNode164 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode163 residual).mapYesStage
    node164FiniteSameInterfaceRetrieval

def node164LocalChecks : Nat := 0

theorem node164LocalChecks_eq_zero : node164LocalChecks = 0 := rfl

#print axioms node164FiniteSameInterfaceRetrieval
#print axioms runInitialThroughNode164

end Erdos64EG.Internal
