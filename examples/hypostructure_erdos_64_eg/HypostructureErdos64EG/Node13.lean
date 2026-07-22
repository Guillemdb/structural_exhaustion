import Hypostructure.Core.Metadata
import Hypostructure.Graph.Replacement
import HypostructureErdos64EG.Node12

/-!
# Diagram node 13: replacement lemma

Graph owns the replacement contradiction.  Under unrestricted boundary
gluing, the current checked framework requires the boundary-overlap count
against the literal outside context in addition to the paper's
boundary-degree equality.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- The minimal context inherited through node 12 by a framework query. -/
def node4ContextAtNode12Query :
    Core.Residual.Focus.ActiveQuery Node12Focus.{u, v}
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode10Query.preserve.preserve

/-- Exact accumulated stage emitted by Graph's replacement executor. -/
abbrev Node13Stage :=
  Graph.FocusedAtomReplacementStage Node12Focus.{u, v}
    node4ContextAtNode12Query

/-- Counted node-13 execution, including inactive sibling outcomes. -/
noncomputable def node13Counted (previous : Node12Stage.{u, v}) :=
  Graph.executeFocusedAtomReplacementCounted Node12Focus.{u, v}
    node4ContextAtNode12Query targetIsomorphismInvariant previous

/-- Execute the replacement contradiction from the literal node-12 stage. -/
noncomputable def node13 (previous : Node12Stage.{u, v}) :
    Node13Stage.{u, v} :=
  (node13Counted previous).value

/-- Focus inherited by the uncompressibility node. -/
abbrev Node13Focus :=
  Core.Residual.ProofProjection.Profile Node12Focus.{u, v}
    (Graph.FocusedAtomReplacementClaim Node12Focus.{u, v}
      node4ContextAtNode12Query)

/-- Query Graph's replacement contradiction from the newest ledger entry. -/
def node13ReplacementQuery :=
  Graph.focusedAtomReplacementQuery Node12Focus.{u, v}
    node4ContextAtNode12Query

/-- Query the private Core proof-projection certificate introduced by node 13. -/
def node13CertificateQuery :=
  Core.Residual.ProofProjection.latest Node12Focus.{u, v}
    (Graph.FocusedAtomReplacementClaim Node12Focus.{u, v}
      node4ContextAtNode12Query)

@[simp] theorem node13_previous (previous : Node12Stage.{u, v}) :
    (node13 previous).previous = previous :=
  rfl

/-- Any same-interface replacement certificate satisfying Graph's complete
overlap-aware hypotheses contradicts minimality. -/
theorem node13_replacement (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    let ctx := node4ContextAtNode12Query.read stage.previous active
    forall (atom : Graph.ProperBoundariedAtom ctx.G)
      (replacement : Graph.BoundaryPiece atom.decomposition.interface),
        Graph.AtomReplacementCertificate ctx atom replacement -> False :=
  node13ReplacementQuery.read stage active

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node13Counted_checks_eq_one
    (previous : Node12Stage.{u, v}) :
    (node13Counted previous).checks = 1 := by
  change
    (Graph.executeFocusedAtomReplacementCounted Node12Focus.{u, v}
      node4ContextAtNode12Query targetIsomorphismInvariant previous).checks = 1
  rw [Graph.executeFocusedAtomReplacementCounted_checks]
  rfl

theorem node13Counted_work_bounded (previous : Node12Stage.{u, v}) :
    (node13Counted previous).checks <=
      (Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}).coefficient *
        ((Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}).size
          previous + 1) ^
            (Core.Residual.ProofProjection.workBudget
              Node12Focus.{u, v}).degree :=
  Graph.executeFocusedAtomReplacementCounted_checks_bounded Node12Focus.{u, v}
    node4ContextAtNode12Query targetIsomorphismInvariant previous

@[simp] theorem node13_checks_eq_one (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    (node13CertificateQuery.read stage active).checks = 1 := by
  exact (node13CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The single focused proof projection satisfies its Core-owned polynomial
envelope. -/
theorem node13_work_bounded (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    (node13CertificateQuery.read stage active).checks <=
      (Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}).coefficient *
        ((Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}).size
          stage.previous + 1) ^
            (Core.Residual.ProofProjection.workBudget
              Node12Focus.{u, v}).degree :=
  (node13CertificateQuery.read stage active).work_bounded

/-- Metadata marker for the currently open boundary-overlap repair required
to recover the literal paper statement under unrestricted gluing. -/
def node13BoundaryOverlapObligation : Core.Metadata.ManualObligation where
  source :=
    ⟨"original_erdos_64_proof.tex", "lem:replacement"⟩
  Claim := True

/-- Proof-relevant audit record for node-13 replacement projection. -/
noncomputable def node13Metadata :
    Core.Metadata.DeclarationMetadata.{
      max (u + 1) (v + 1), 0, max (u + 1) (v + 1)}
      Node12Stage.{u, v} Node12Stage.{u, v} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node13", "node13Counted"⟩
  primitiveInputs := []
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node12", "node12"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node13",
      "node4ContextAtNode12Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.Graph.Replacement",
      "executeFocusedAtomReplacementCounted"⟩,
    ⟨"Hypostructure.Graph.Replacement",
      "AtomReplacementCertificate.impossible"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Certificate"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Stage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.Replacement",
      "AtomReplacementCertificate.gluedReplacement_smaller"⟩,
    ⟨"Hypostructure.Graph.BoundaryOverlap",
      "glue_lexicographicallySmaller_of_local_of_overlapCount_eq"⟩,
    ⟨"Hypostructure.Core.Residual.ProofProjection",
      "executeCounted_checks_bounded"⟩
  ]
  closureMechanisms := [
    .strictProgress
  ]
  workBound := Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}
  manualObligations := [
    node13BoundaryOverlapObligation
  ]

/-- The current checked node deliberately records the paper/framework
boundary-overlap residual instead of representing it as solved. -/
theorem node13_metadata_has_boundary_overlap_obligation :
    node13Metadata.manualObligations =
      [node13BoundaryOverlapObligation] :=
  rfl

#print axioms node13
#print axioms node13_replacement
#print axioms node13Counted_checks_eq_one
#print axioms node13Counted_work_bounded
#print axioms node13_checks_eq_one
#print axioms node13_work_bounded
#print axioms node13_metadata_has_boundary_overlap_obligation

end HypostructureErdos64EG
