import Hypostructure.Core.Metadata
import Hypostructure.Graph.Replacement
import HypostructureErdos64EG.Node12

/-!
# Diagram node 13: replacement lemma

Graph owns the normalized replacement contradiction.  The EG instantiation
uses the paper convention that boundary--boundary edges of an atom
decomposition are assigned to the atom side, so the node exposes the same
replacement certificate shape as the legacy implementation without an
application-owned overlap residual.
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
  Graph.FocusedNormalizedAtomReplacementStage Node12Focus.{u, v}
    node4ContextAtNode12Query egNormalizedAtomReplacementProfile

/-- Counted node-13 execution, including inactive sibling outcomes. -/
noncomputable def node13Counted (previous : Node12Stage.{u, v}) :=
  Graph.executeFocusedNormalizedAtomReplacementCounted Node12Focus.{u, v}
    node4ContextAtNode12Query egNormalizedAtomReplacementProfile
    baselineIsomorphismInvariant targetIsomorphismInvariant previous

/-- Execute the replacement contradiction from the literal node-12 stage. -/
noncomputable def node13 (previous : Node12Stage.{u, v}) :
    Node13Stage.{u, v} :=
  (node13Counted previous).value

/-- Focus inherited by the uncompressibility node. -/
abbrev Node13Focus :=
  Core.Residual.ProofProjection.Profile Node12Focus.{u, v}
    (Graph.FocusedNormalizedAtomReplacementClaim Node12Focus.{u, v}
      node4ContextAtNode12Query egNormalizedAtomReplacementProfile)

/-- Query Graph's replacement contradiction from the newest ledger entry. -/
def node13ReplacementQuery :=
  Graph.focusedNormalizedAtomReplacementQuery Node12Focus.{u, v}
    node4ContextAtNode12Query egNormalizedAtomReplacementProfile

/-- Query the private Core proof-projection certificate introduced by node 13. -/
def node13CertificateQuery :=
  Core.Residual.ProofProjection.latest Node12Focus.{u, v}
    (Graph.FocusedNormalizedAtomReplacementClaim Node12Focus.{u, v}
      node4ContextAtNode12Query egNormalizedAtomReplacementProfile)

/-- Canonical work budget for the node-13 proof projection. -/
abbrev node13WorkBudget :=
  Core.Residual.ProofProjection.workBudget Node12Focus.{u, v}

@[simp] theorem node13_previous (previous : Node12Stage.{u, v}) :
    (node13 previous).previous = previous :=
  rfl

/-- Any same-interface replacement certificate satisfying Graph's normalized
hypotheses contradicts minimality. -/
theorem node13_replacement (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    let ctx := node4ContextAtNode12Query.read stage.previous active
    forall (atom : Graph.NormalizedProperBoundariedAtom ctx.G)
      (replacement : Graph.BoundaryPiece atom.toAtom.decomposition.interface),
        Graph.NormalizedAtomReplacementCertificate
          egNormalizedAtomReplacementProfile ctx atom replacement -> False :=
  node13ReplacementQuery.read stage active

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node13Counted_checks_eq_one
    (previous : Node12Stage.{u, v}) :
    (node13Counted previous).checks = 1 := by
  change
    (Graph.executeFocusedNormalizedAtomReplacementCounted Node12Focus.{u, v}
      node4ContextAtNode12Query egNormalizedAtomReplacementProfile
      baselineIsomorphismInvariant targetIsomorphismInvariant previous).checks = 1
  rw [Graph.executeFocusedNormalizedAtomReplacementCounted_checks]
  rfl

theorem node13Counted_work_bounded (previous : Node12Stage.{u, v}) :
    node13WorkBudget.Within previous (node13Counted previous).checks :=
  Graph.executeFocusedNormalizedAtomReplacementCounted_work_within
    Node12Focus.{u, v} node4ContextAtNode12Query
    egNormalizedAtomReplacementProfile baselineIsomorphismInvariant
    targetIsomorphismInvariant previous

@[simp] theorem node13_checks_eq_one (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    (node13CertificateQuery.read stage active).checks = 1 := by
  exact (node13CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The single focused proof projection satisfies its Core-owned polynomial
envelope. -/
theorem node13_work_bounded (stage : Node13Stage.{u, v})
    (active : Node13Focus.Active stage) :
    node13WorkBudget.Within stage.previous
      (node13CertificateQuery.read stage active).checks :=
  (node13CertificateQuery.read stage active).work_within

/-- Proof-relevant audit record for node-13 replacement projection. -/
noncomputable def node13Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, 0, u + 1}
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
      "executeFocusedNormalizedAtomReplacementCounted"⟩,
    ⟨"Hypostructure.Graph.Replacement",
      "NormalizedAtomReplacementCertificate.impossible"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Certificate"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Stage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.Replacement",
      "NormalizedAtomReplacementCertificate.toAtomReplacementCertificate"⟩,
    ⟨"Hypostructure.Graph.BoundaryOverlap",
      "glue_lexicographicallySmaller_of_local_of_context_noBoundaryEdges"⟩,
    ⟨"Hypostructure.Graph.BoundaryOverlap",
      "glue_minDegree_ge_of_local_boundary_eq_of_context_noBoundaryEdges"⟩,
    ⟨"Hypostructure.Core.Residual.ProofProjection",
      "executeCounted_work_within"⟩
  ]
  closureMechanisms := [
    .strictProgress
  ]
  workBound := node13WorkBudget
  manualObligations := []

/-- Node 13 has no unrecorded mathematical or routing obligation. -/
def node13MetadataComplete :
    Core.Metadata.Complete node13Metadata :=
  ⟨rfl⟩

theorem node13_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node13Metadata.manualObligations) :=
  node13MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused proof-projection work bound used by
the executor. -/
theorem node13_metadata_work_bounded (previous : Node12Stage.{u, v}) :
    node13Metadata.workBound.Within previous
      (node13Metadata.workBound.checks previous) :=
  node13MetadataComplete.work_within previous

#print axioms node13
#print axioms node13_replacement
#print axioms node13Counted_checks_eq_one
#print axioms node13Counted_work_bounded
#print axioms node13_checks_eq_one
#print axioms node13_work_bounded
#print axioms node13_metadata_has_no_manual_obligation
#print axioms node13_metadata_work_bounded

end HypostructureErdos64EG
