import Erdos64EG.Node160

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [162]: exact CT3 residual extraction

Node [162] consumes the no side of node [160].  It exposes the exact CT3
residual object already carried by the
framework run: either a distinguishing-context residual or a novel-row
residual.  A later route may consume this exact residual and send it to the
hot branch if such a framework route is available.
-/

abbrev Node162ExactCT3ResidualOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_hasResidual : Node160HasCT3Residual active) : Prop :=
    ∃ entry ∈ node152BranchExcessSchedule active.data.data.data,
      (∃ _ct3Residual :
        CT3.DistinguishingContextResidual (node159Spec active.data entry)
          (node159Capability active.data entry) (node159Input active.data entry),
        (node159Run active.data entry).terminal = .distinguishing) ∨
      (∃ table,
        ∃ _ct3Residual :
          CT3.NovelExternalTypeResidual (node159Spec active.data entry)
            (node159Capability active.data entry) (node159Input active.data entry)
            table,
          (node159Run active.data entry).terminal = .novelRow)

abbrev Node162Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node162ExactCT3ResidualOutput V) residual

noncomputable def node162ExactCT3ResidualRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node160ResidualStage V))
        facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node162Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := @Node160CT3ResidualOutput V)
    (Next := @Node162ExactCT3ResidualOutput V)
    fun _residual active hasResidual node160 => by
      let entry := Classical.choose node160
      have entrySpec := Classical.choose_spec node160
      have member := entrySpec.1
      have terminalResidual := entrySpec.2
      refine ⟨entry, member, ?_⟩
      cases runEq : node159Run active.data entry with
      | mk terminal path outcome =>
      cases outcome with
      | compression certificate =>
          rw [runEq] at terminalResidual
          simp at terminalResidual
      | distinguishing residual =>
          exact Or.inl ⟨residual, rfl⟩
      | knownRow certificate =>
          rw [runEq] at terminalResidual
          simp at terminalResidual
      | novelRow residual =>
          exact Or.inr ⟨_, residual, rfl⟩

noncomputable def runInitialThroughNode162 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode160Residual residual).mapYesStage
    node162ExactCT3ResidualRefinement

def node162LocalChecks : Nat := 0

theorem node162LocalChecks_eq_zero : node162LocalChecks = 0 := rfl

#print axioms node162ExactCT3ResidualRefinement
#print axioms runInitialThroughNode162

end Erdos64EG.Internal
