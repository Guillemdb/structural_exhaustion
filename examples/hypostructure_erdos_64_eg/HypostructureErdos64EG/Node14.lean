import Hypostructure.Core.Metadata
import Hypostructure.Graph.Replacement
import HypostructureErdos64EG.Node13

/-!
# Diagram node 14: hereditary target-uncompressibility

Graph owns the corollary projection from the replacement contradiction and
context universality.  This node only preserves the predecessor-owned context,
registration, replacement, and universality queries through node 13 and invokes
the generic Graph executor.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- The minimal context inherited through node 13 by a framework query. -/
def node4ContextAtNode13Query :
    Core.Residual.Focus.ActiveQuery Node13Focus.{u, v}
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode12Query.preserve

/-- Node-11's exact atom-profile registration, preserved through nodes 12 and
13 without copying the registration payload. -/
def node11RegistrationAtNode13Query :
    Core.Residual.Focus.ActiveQuery Node13Focus.{u, v}
      (fun stage active =>
        Graph.BoundariedAtomRegistration
          (node4ContextAtNode13Query.read stage active)) :=
  node11RegistrationQuery.preserve.preserve

/-- Node-13's replacement contradiction, reindexed to the node-13 focus for
the Graph-owned uncompressibility executor. -/
def node13ReplacementAtNode13Query :
    Core.Residual.Focus.ActiveQuery Node13Focus.{u, v}
      (Graph.FocusedNormalizedAtomReplacementClaim Node13Focus.{u, v}
        node4ContextAtNode13Query egNormalizedAtomReplacementProfile) :=
  node13ReplacementQuery

/-- Node-12 context universality, reindexed to the node-13 focus and Node-11's
preserved registration. -/
def node12ContextUniversalityAtNode13Query :
    Core.Residual.Focus.ActiveQuery Node13Focus.{u, v}
      (Graph.FocusedRegisteredContextUniversalityClaim.{
        u, 0, v, u + 1}
        Node13Focus.{u, v} node4ContextAtNode13Query
        node11RegistrationAtNode13Query) :=
  node12ContextUniversalityQuery.preserve

/-- Exact accumulated stage emitted by Graph's uncompressibility executor. -/
abbrev Node14Stage :=
  Graph.FocusedNormalizedAtomUncompressibilityStage.{
    u, 0, v, u + 1}
    Node13Focus.{u, v} node4ContextAtNode13Query
    egNormalizedAtomReplacementProfile node11RegistrationAtNode13Query

/-- Counted node-14 execution, including inactive sibling outcomes. -/
noncomputable def node14Counted (previous : Node13Stage.{u, v}) :=
  Graph.executeFocusedNormalizedAtomUncompressibilityCounted.{
    u, 0, v, u + 1}
    Node13Focus.{u, v} node4ContextAtNode13Query
    egNormalizedAtomReplacementProfile node11RegistrationAtNode13Query
    node13ReplacementAtNode13Query node12ContextUniversalityAtNode13Query
    previous

/-- Execute the uncompressibility corollary from the literal node-13 stage. -/
noncomputable def node14 (previous : Node13Stage.{u, v}) :
    Node14Stage.{u, v} :=
  (node14Counted previous).value

/-- Focus inherited by the next node. -/
abbrev Node14Focus :=
  Core.Residual.ProofProjection.Profile Node13Focus.{u, v}
    (Graph.FocusedNormalizedAtomUncompressibilityClaim.{
      u, 0, v, u + 1}
      Node13Focus.{u, v}
      node4ContextAtNode13Query egNormalizedAtomReplacementProfile
      node11RegistrationAtNode13Query)

/-- Query Graph's hereditary uncompressibility corollary from the newest
ledger entry. -/
def node14UncompressibilityQuery :
    Core.Residual.Focus.ActiveQuery Node14Focus.{u, v}
      (fun stage active =>
        Graph.FocusedNormalizedAtomUncompressibilityClaim.{
          u, 0, v, u + 1}
          Node13Focus.{u, v} node4ContextAtNode13Query
          egNormalizedAtomReplacementProfile node11RegistrationAtNode13Query
          stage.previous active) :=
  Graph.focusedNormalizedAtomUncompressibilityQuery.{
    u, 0, u + 1, v}
    Node13Focus.{u, v}
    node4ContextAtNode13Query egNormalizedAtomReplacementProfile
    node11RegistrationAtNode13Query

/-- Query the private Core proof-projection certificate introduced by node 14. -/
def node14CertificateQuery :=
  Core.Residual.ProofProjection.latest Node13Focus.{u, v}
    (Graph.FocusedNormalizedAtomUncompressibilityClaim.{
      u, 0, v, u + 1}
      Node13Focus.{u, v}
      node4ContextAtNode13Query egNormalizedAtomReplacementProfile
      node11RegistrationAtNode13Query)

/-- Canonical work budget for the node-14 proof projection. -/
abbrev node14WorkBudget :=
  Core.Residual.ProofProjection.workBudget Node13Focus.{u, v}

@[simp] theorem node14_previous (previous : Node13Stage.{u, v}) :
    (node14 previous).previous = previous :=
  rfl

/-- No proper normalized atom admits a nontrivial target-complete replacement
compression. -/
theorem node14_noTargetCompleteCompression (stage : Node14Stage.{u, v})
    (active : Node14Focus.Active stage) :
    let ctx := node4ContextAtNode13Query.read stage.previous active
    forall (atom : Graph.NormalizedProperBoundariedAtom ctx.G)
      (replacement : Graph.BoundaryPiece atom.toAtom.decomposition.interface),
        Graph.NormalizedAtomReplacementCertificate
          egNormalizedAtomReplacementProfile ctx atom replacement -> False :=
  (node14UncompressibilityQuery.read stage active).1

/-- A registered coordinate identification that is not context-universal is
not target-complete and has an explicit distinguishing outside context. -/
theorem node14_defectiveIdentification (stage : Node14Stage.{u, v})
    (active : Node14Focus.Active stage) :
    forall (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode13Query.read stage.previous active).G)
      (system : Graph.AtomResponse.CoordinateSystem.{u, v}
        ((node11RegistrationAtNode13Query.read stage.previous active).family
          atom) Target)
      {left right : system.Coordinate},
        Not (system.ContextEquivalent left right) ->
          Not (Graph.AtomResponse.TargetCompleteIdentification system
            left right) ∧
            Graph.AtomResponse.TargetDefect system left right :=
  (node14UncompressibilityQuery.read stage active).2

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node14Counted_checks_eq_one
    (previous : Node13Stage.{u, v}) :
    (node14Counted previous).checks = 1 := by
  change
    (Graph.executeFocusedNormalizedAtomUncompressibilityCounted.{
      u, 0, v, u + 1}
      Node13Focus.{u, v} node4ContextAtNode13Query
      egNormalizedAtomReplacementProfile node11RegistrationAtNode13Query
      node13ReplacementAtNode13Query node12ContextUniversalityAtNode13Query
      previous).checks = 1
  rw [Graph.executeFocusedNormalizedAtomUncompressibilityCounted_checks]
  rfl

theorem node14Counted_work_bounded (previous : Node13Stage.{u, v}) :
    node14WorkBudget.Within previous (node14Counted previous).checks :=
  Graph.executeFocusedNormalizedAtomUncompressibilityCounted_work_within.{
    u, 0, u + 1, v}
    Node13Focus.{u, v} node4ContextAtNode13Query
    egNormalizedAtomReplacementProfile node11RegistrationAtNode13Query
    node13ReplacementAtNode13Query node12ContextUniversalityAtNode13Query
    previous

@[simp] theorem node14_checks_eq_one (stage : Node14Stage.{u, v})
    (active : Node14Focus.Active stage) :
    (node14CertificateQuery.read stage active).checks = 1 := by
  exact (node14CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The single focused proof projection satisfies its Core-owned polynomial
envelope. -/
theorem node14_work_bounded (stage : Node14Stage.{u, v})
    (active : Node14Focus.Active stage) :
    node14WorkBudget.Within stage.previous
      (node14CertificateQuery.read stage active).checks :=
  (node14CertificateQuery.read stage active).work_within

/-- Proof-relevant audit record for node-14 uncompressibility projection. -/
noncomputable def node14Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, 0, u + 1}
      Node13Stage.{u, v} Node13Stage.{u, v} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node14", "node14Counted"⟩
  primitiveInputs := []
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node13", "node13"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node14",
      "node4ContextAtNode13Query"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node14",
      "node11RegistrationAtNode13Query"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node14",
      "node13ReplacementAtNode13Query"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node14",
      "node12ContextUniversalityAtNode13Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.Graph.Replacement",
      "executeFocusedNormalizedAtomUncompressibilityCounted"⟩,
    ⟨"Hypostructure.Graph.Replacement",
      "focusedNormalizedAtomUncompressibilityProjectionQuery"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Certificate"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Stage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.AtomResponse",
      "targetDefect_of_not_contextEquivalent"⟩,
    ⟨"Hypostructure.Core.Residual.ProofProjection",
      "executeCounted_work_within"⟩
  ]
  closureMechanisms := [
    .strictProgress
  ]
  workBound := node14WorkBudget
  manualObligations := []

/-- Node 14 has no unrecorded mathematical or routing obligation. -/
def node14MetadataComplete :
    Core.Metadata.Complete node14Metadata :=
  ⟨rfl⟩

theorem node14_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node14Metadata.manualObligations) :=
  node14MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused proof-projection work bound used by
the executor. -/
theorem node14_metadata_work_bounded (previous : Node13Stage.{u, v}) :
    node14Metadata.workBound.Within previous
      (node14Metadata.workBound.checks previous) :=
  node14MetadataComplete.work_within previous

#print axioms node14
#print axioms node14_noTargetCompleteCompression
#print axioms node14_defectiveIdentification
#print axioms node14Counted_checks_eq_one
#print axioms node14Counted_work_bounded
#print axioms node14_checks_eq_one
#print axioms node14_work_bounded
#print axioms node14_metadata_has_no_manual_obligation
#print axioms node14_metadata_work_bounded

end HypostructureErdos64EG
