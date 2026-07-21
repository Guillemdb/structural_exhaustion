import Erdos64EG.Node161

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [163]: CT3 good-terminal replacement extraction

Node [163] consumes the yes side of node [161].  It extracts the common
framework fact supplied by both
CT3 good terminals: a predecessor-owned candidate length that is positive,
strictly shorter than the source, and has the same finite response vector.
-/

abbrev Node163StrictResponseReplacementOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_allGood : Node160AllCompressionOrKnown active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
      ∃ candidate : Node159Candidate active.data entry,
        0 < candidate.1.1 ∧
          candidate.1.1 < node159SourceLength active.data entry ∧
          CT3.SameResponse (node159Spec active.data entry)
            candidate.1.1 (node159SourceLength active.data entry)

abbrev Node163Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node163StrictResponseReplacementOutput V) residual

noncomputable def node163StrictResponseReplacementContinuation {V : Type u}
    {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node161Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node163Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := @Node161CompressionStyleOutput V)
    (Next := @Node163StrictResponseReplacementOutput V)
    fun _residual active _allGood node161 => by
      intro entry member
      rcases node161 entry member with
        ⟨candidate, compresses⟩ | ⟨row, rowMatches⟩
      · let replacement :=
          CT3.strictResponseReplacement_of_compresses
            (S := node159Spec active.data entry)
            (input := node159Input active.data entry) compresses
        exact
          ⟨replacement.candidate, replacement.admissible,
            replacement.smaller, replacement.sameResponse⟩
      · let replacement :=
          CT3.strictResponseReplacement_of_rowMatches
            (S := node159Spec active.data entry)
            (input := node159Input active.data entry)
            (node159RowCandidateEmbedding active.data entry) rowMatches
        exact
          ⟨replacement.candidate, replacement.admissible,
            replacement.smaller, replacement.sameResponse⟩

noncomputable def runInitialThroughNode163 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode161 residual).mapYesStage
    node163StrictResponseReplacementContinuation

def node163LocalChecks : Nat := 0

theorem node163LocalChecks_eq_zero : node163LocalChecks = 0 := rfl

#print axioms node163StrictResponseReplacementContinuation
#print axioms runInitialThroughNode163

end Erdos64EG.Internal
