import Hypostructure.Core.Metadata
import Hypostructure.Graph.DeletionCriticality
import HypostructureErdos64EG.Node8

/-!
# Diagram node 9: edge-deletion criticality

The Graph layer consumes node 8's minimal context and no-proper-core
certificate through typed ledger queries.  The EG application supplies only
the official minimum-degree threshold.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Official minimum-degree threshold used by the paper at node 9. -/
def node9MinimumDegreeThreshold : Nat := 3

/-- Minimal context inherited through node 8 by a framework query. -/
def node4ContextAtNode8Query :
    Core.Residual.Focus.ActiveQuery Node8Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous.previous.previous active) :=
  node4ContextAtNode6AvoidingQuery.preserve

/-- Exact accumulated stage emitted by Graph's deletion-criticality executor. -/
abbrev Node9Stage :=
  Graph.FocusedMinimumDegreeDeletionCriticalityStage
    node9MinimumDegreeThreshold Node8Focus node4ContextAtNode8Query

/-- Counted node-9 execution from the literal node-8 predecessor. -/
noncomputable def node9Counted (previous : Node8Stage.{u}) :
    Core.Counted Node9Stage.{u} :=
  Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted
    node9MinimumDegreeThreshold Node8Focus node4ContextAtNode8Query
    node8CertificateQuery previous

/-- Execute node 9 from the literal node-8 predecessor. -/
noncomputable def node9 (previous : Node8Stage.{u}) : Node9Stage.{u} :=
  (node9Counted previous).value

/-- Focus inherited by node 10. -/
abbrev Node9Focus :=
  Graph.FocusedMinimumDegreeDeletionCriticalityProfile
    node9MinimumDegreeThreshold Node8Focus node4ContextAtNode8Query

/-- Query Graph's generated endpoint-criticality certificate. -/
def node9CertificateQuery :=
  Graph.focusedMinimumDegreeDeletionCriticalityQuery
    node9MinimumDegreeThreshold Node8Focus node4ContextAtNode8Query

@[simp] theorem node9_previous (previous : Node8Stage.{u}) :
    (node9 previous).previous = previous :=
  rfl

/-- Every edge has a degree-three endpoint. -/
theorem node9_edge_touches_degree_three (stage : Node9Stage.{u})
    (active : Node9Focus.Active stage)
    (dart : (node4ContextAtNode8Query.read stage.previous active).G.graph.Dart) :
    (node4ContextAtNode8Query.read stage.previous active).G.degree dart.fst = 3 ∨
      (node4ContextAtNode8Query.read stage.previous active).G.degree dart.snd = 3 :=
  by
    simpa [node9MinimumDegreeThreshold,
      Graph.minimumDegreeDeletionCriticalityProfile] using
      (node9CertificateQuery.read stage active).tightEndpoint dart

theorem node9Counted_work_bounded (previous : Node8Stage.{u}) :
    Node8Focus.selectionBudget.Within previous
      (node9Counted previous).checks :=
  Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted_work_within
    node9MinimumDegreeThreshold Node8Focus node4ContextAtNode8Query
    node8CertificateQuery previous

/-- Proof-relevant audit record for node-9 deletion criticality. -/
noncomputable def node9Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node8Stage.{u} Node8Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node9", "node9Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node9",
      "node9MinimumDegreeThreshold"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node8", "node8"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node8", "node8CertificateQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node9",
      "node4ContextAtNode8Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node9",
      "node4ContextAtNode8Query"⟩
    profile := Node8Focus
    Result := fun stage active =>
      Node4Output stage.previous.previous.previous.previous.previous active
    query := node4ContextAtNode8Query
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "executeFocusedMinimumDegreeDeletionCriticalityCounted"⟩,
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "deriveDeletionCriticality"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.DeletionCriticality",
      "DeletionCriticalityCertificate"⟩, .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.DeletionCriticality",
      "FocusedMinimumDegreeDeletionCriticalityStage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "DeletionCriticalityCertificate.tightEndpoint"⟩,
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "executeFocusedMinimumDegreeDeletionCriticalityCounted_work_within"⟩
  ]
  closureMechanisms := [Core.Closure.Mechanism.strictProgress]
  workBound := Node8Focus.selectionBudget
  manualObligations := []

/-- Node 9 has no unrecorded mathematical or routing obligation. -/
def node9MetadataComplete :
    Core.Metadata.Complete node9Metadata :=
  ⟨rfl⟩

theorem node9_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node9Metadata.manualObligations) :=
  node9MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused-selection work bound used by the
executor. -/
theorem node9_metadata_work_bounded (previous : Node8Stage.{u}) :
    node9Metadata.workBound.Within previous
      (node9Metadata.workBound.checks previous) :=
  node9MetadataComplete.work_within previous

#print axioms node9
#print axioms node9Counted_work_bounded
#print axioms node9_edge_touches_degree_three
#print axioms node9_metadata_has_no_manual_obligation
#print axioms node9_metadata_work_bounded

end HypostructureErdos64EG
