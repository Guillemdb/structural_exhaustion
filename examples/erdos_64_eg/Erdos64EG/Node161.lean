import Erdos64EG.Node160

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [161]: CT3 compression-style certificate extraction

Node [161] consumes the yes side of node [160].  It does not create a graph
replacement theorem.  It exposes exactly what CT3 has proved on each scheduled
bounded G3 entry: either a compression candidate satisfying CT3's native
`Compresses` predicate, or a known exact table row satisfying `RowMatches`.
-/

abbrev Node161CompressionStyleOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_allGood : Node160AllCompressionOrKnown active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
      (∃ candidate : (node159Spec active.data entry).Candidate,
        CT3.Compresses (node159Spec active.data entry)
          (node159Input active.data entry) candidate) ∨
      (∃ row : (node159Spec active.data entry).Row,
        CT3.RowMatches (node159Spec active.data entry)
          (node159Input active.data entry) row)

abbrev Node161Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node161CompressionStyleOutput V) residual

noncomputable def node161CompressionStyleContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node160DecisionStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node161Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    (Bypass := Node160Bypass V)
    (Active := Node160Active V)
    (yes := @Node160AllCompressionOrKnown V)
    (no := @Node160HasCT3Residual V)
    (fun _residual active allGood =>
      by
        intro entry member
        have terminalGood := allGood entry member
        cases runEq : node159Run active.data entry with
        | mk terminal path outcome =>
        cases outcome with
        | compression certificate =>
            refine Or.inl ?_
            exact ⟨certificate.candidate, certificate.valid⟩
        | distinguishing residual =>
            rw [runEq] at terminalGood
            simp at terminalGood
        | knownRow certificate =>
            refine Or.inr ?_
            exact ⟨certificate.row, certificate.rowMatches⟩
        | novelRow residual =>
            rw [runEq] at terminalGood
            simp at terminalGood)

noncomputable def runInitialThroughNode161 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode160Decision residual).mapYesStage
    node161CompressionStyleContinuation

def node161LocalChecks : Nat := 0

theorem node161LocalChecks_eq_zero : node161LocalChecks = 0 := rfl

#print axioms node161CompressionStyleContinuation
#print axioms runInitialThroughNode161

end Erdos64EG.Internal
