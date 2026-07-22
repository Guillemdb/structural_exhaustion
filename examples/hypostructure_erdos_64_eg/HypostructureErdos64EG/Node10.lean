import Hypostructure.Core.Metadata
import HypostructureErdos64EG.Node9

/-!
# Diagram node 10: high-degree vertices are independent

Graph derives and registers this consequence of node 9's deletion-criticality
certificate.  No edge argument or proof payload is authored by the EG layer.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context inherited through node 9 by a framework query. -/
def node4ContextAtNode9Query :
    Core.Residual.Focus.ActiveQuery Node9Focus
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode8Query.preserve

/-- Exact accumulated stage emitted by Graph's independence executor. -/
abbrev Node10Stage :=
  Graph.FocusedSlackVertexIndependenceStage Node9Focus
    (Graph.minimumDegreeDeletionCriticalityProfile node9MinimumDegreeThreshold)
    node4ContextAtNode9Query

/-- Counted node-10 execution from the literal node-9 predecessor. -/
noncomputable def node10Counted (previous : Node9Stage.{u}) :
    Core.Counted Node10Stage.{u} :=
  Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted
    node9MinimumDegreeThreshold Node9Focus node4ContextAtNode9Query
    node9CertificateQuery previous

/-- Execute node 10 from the literal node-9 predecessor. -/
noncomputable def node10 (previous : Node9Stage.{u}) : Node10Stage.{u} :=
  (node10Counted previous).value

/-- Focus inherited by node 11. -/
abbrev Node10Focus :=
  Graph.FocusedSlackVertexIndependenceProfile Node9Focus
    (Graph.minimumDegreeDeletionCriticalityProfile node9MinimumDegreeThreshold)
    node4ContextAtNode9Query

/-- Query Graph's registered independence fact. -/
def node10IndependenceQuery :=
  Graph.focusedMinimumDegreeSlackVertexIndependenceQuery
    node9MinimumDegreeThreshold Node9Focus node4ContextAtNode9Query

@[simp] theorem node10_previous (previous : Node9Stage.{u}) :
    (node10 previous).previous = previous :=
  rfl

/-- Vertices of degree at least four form an independent set. -/
theorem node10_high_degree_vertices_independent (stage : Node10Stage.{u})
    (active : Node10Focus.Active stage)
    {left right : (node4ContextAtNode9Query.read stage.previous active).G.Vertex}
    (leftHigh :
      4 ≤ (node4ContextAtNode9Query.read stage.previous active).G.degree left)
    (rightHigh :
      4 ≤ (node4ContextAtNode9Query.read stage.previous active).G.degree right) :
    Not ((node4ContextAtNode9Query.read stage.previous active).G.graph.Adj
      left right) :=
  by
    simpa [node9MinimumDegreeThreshold,
      Graph.minimumDegreeDeletionCriticalityProfile] using
      node10IndependenceQuery.read stage active leftHigh rightHigh

theorem node10Counted_work_bounded (previous : Node9Stage.{u}) :
    Node9Focus.selectionBudget.Within previous
      (node10Counted previous).checks :=
  Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted_work_within
    node9MinimumDegreeThreshold Node9Focus node4ContextAtNode9Query
    node9CertificateQuery previous

/-- Proof-relevant audit record for node-10 slack-vertex independence. -/
noncomputable def node10Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node9Stage.{u} Node9Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node10", "node10Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node9",
      "node9MinimumDegreeThreshold"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node9", "node9"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node9", "node9CertificateQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node10",
      "node4ContextAtNode9Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node10",
      "node4ContextAtNode9Query"⟩
    profile := Node9Focus
    Result := fun _stage _active =>
      Core.MinimalCounterexampleContext problem Target EGProgress
    query := node4ContextAtNode9Query
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "executeFocusedMinimumDegreeSlackVertexIndependenceCounted"⟩,
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "deriveSlackVertexIndependence"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.DeletionCriticality",
      "SlackVertexIndependence"⟩, .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.DeletionCriticality",
      "FocusedSlackVertexIndependenceStage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "DeletionCriticalityCertificate.slackVerticesIndependent"⟩,
    ⟨"Hypostructure.Graph.DeletionCriticality",
      "executeFocusedMinimumDegreeSlackVertexIndependenceCounted_work_within"⟩
  ]
  closureMechanisms := []
  workBound := Node9Focus.selectionBudget
  manualObligations := []

/-- Node 10 has no unrecorded mathematical or routing obligation. -/
def node10MetadataComplete :
    Core.Metadata.Complete node10Metadata :=
  ⟨rfl⟩

theorem node10_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node10Metadata.manualObligations) :=
  node10MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused-selection work bound used by the
executor. -/
theorem node10_metadata_work_bounded (previous : Node9Stage.{u}) :
    node10Metadata.workBound.Within previous
      (node10Metadata.workBound.checks previous) :=
  node10MetadataComplete.work_within previous

#print axioms node10
#print axioms node10Counted_work_bounded
#print axioms node10_high_degree_vertices_independent
#print axioms node10_metadata_has_no_manual_obligation
#print axioms node10_metadata_work_bounded

end HypostructureErdos64EG
