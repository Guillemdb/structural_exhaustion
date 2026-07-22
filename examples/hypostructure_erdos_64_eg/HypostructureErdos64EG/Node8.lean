import Hypostructure.Core.Metadata
import Hypostructure.Graph.Minimality
import HypostructureErdos64EG.Node6

/-!
# Diagram node 8: no proper minimum-degree-three subgraph

The Graph layer applies strict-progress minimality to every certified proper
subgraph on node 6's exact avoiding residual. The application supplies only
the EG baseline, branch-state initializer, and cycle target.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context lifted through node 6's avoiding residual without copying. -/
def node4ContextAtNode6AvoidingQuery :
    Core.Residual.Focus.ActiveQuery Node6AvoidingFocus
      (fun stage active =>
        Node4Output stage.previous.previous.previous.previous active) :=
  node4ContextAtNode6Query.preserve

/-- EG instantiation of Graph's generic cycle-target proper-subgraph profile. -/
def node8MinimalityProfile :
    Graph.ProperSubgraphMinimalityProfile Baseline BranchState Target :=
  Graph.cycleProperSubgraphMinimalityProfile Baseline BranchState
    PowerOfTwoLength (fun _object => ())

/-- Exact accumulated stage emitted by Graph's focused executor. -/
abbrev Node8Stage :=
  Graph.FocusedNoProperBaselineStage Node6AvoidingFocus
    node4ContextAtNode6AvoidingQuery

/-- Counted node-8 execution on the framework-owned node-6 avoiding residual. -/
noncomputable def node8Counted
    (previous : Node6AvoidingStage.{u}) : Core.Counted Node8Stage.{u} :=
  Graph.executeFocusedNoProperBaselineCounted Node6AvoidingFocus
    node8MinimalityProfile
    node4ContextAtNode6AvoidingQuery previous

/-- Execute node 8 on the framework-owned node-6 avoiding residual. -/
noncomputable def node8
    (previous : Node6AvoidingStage.{u}) : Node8Stage.{u} :=
  (node8Counted previous).value

/-- Focus inherited by node 9. -/
abbrev Node8Focus :=
  Graph.FocusedNoProperBaselineProfile Node6AvoidingFocus
    node4ContextAtNode6AvoidingQuery

/-- Typed query for Graph's framework-owned no-proper-core certificate. -/
def node8CertificateQuery :=
  Graph.focusedNoProperBaselineQuery Node6AvoidingFocus
    node4ContextAtNode6AvoidingQuery

@[simp] theorem node8_previous (previous : Node6AvoidingStage.{u}) :
    (node8 previous).previous = previous :=
  rfl

/-- Every certified proper subgraph fails the minimum-degree-three baseline. -/
theorem node8_noProperCore (stage : Node8Stage.{u})
    (active : Node8Focus.Active stage)
    (subgraph : Graph.ProperSubgraph
      (node4ContextAtNode6AvoidingQuery.read stage.previous active).G) :
    Not (Baseline subgraph.value) :=
  (node8CertificateQuery.read stage active).excludes subgraph

/-- Every hypothetical proper core closes by Core's strict-progress mechanism. -/
theorem node8_closure_mechanism (stage : Node8Stage.{u})
    (active : Node8Focus.Active stage)
    (subgraph : Graph.ProperSubgraph
      (node4ContextAtNode6AvoidingQuery.read stage.previous active).G)
    (baseline : Baseline subgraph.value) :
    ((node8CertificateQuery.read stage active).closure subgraph baseline).mechanism =
      Core.Closure.Mechanism.strictProgress :=
  (node8CertificateQuery.read stage active).mechanism subgraph baseline

theorem node8Counted_work_bounded (previous : Node6AvoidingStage.{u}) :
    Node6AvoidingFocus.selectionBudget.Within previous
      (node8Counted previous).checks :=
  Graph.executeFocusedNoProperBaselineCounted_work_within
    Node6AvoidingFocus node8MinimalityProfile
      node4ContextAtNode6AvoidingQuery previous

/-- Proof-relevant audit record for node-8 focused proper-subgraph
minimality. -/
noncomputable def node8Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node6AvoidingStage.{u} Node6AvoidingStage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node8", "node8Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node8", "node8MinimalityProfile"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node6", "node6ContinueAvoiding"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node8",
      "node4ContextAtNode6AvoidingQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node8",
      "node4ContextAtNode6AvoidingQuery"⟩
    profile := Node6AvoidingFocus
    Result := fun stage active =>
      Node4Output stage.previous.previous.previous.previous active
    query := node4ContextAtNode6AvoidingQuery
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.Minimality",
      "executeFocusedNoProperBaselineCounted"⟩,
    ⟨"Hypostructure.Graph.Minimality", "deriveNoProperBaseline"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.Minimality",
      "NoProperBaselineCertificate"⟩, .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.Minimality",
      "FocusedNoProperBaselineStage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.Minimality",
      "NoProperBaselineCertificate.excludes"⟩,
    ⟨"Hypostructure.Graph.Minimality",
      "executeFocusedNoProperBaselineCounted_work_within"⟩,
    ⟨"Hypostructure.Core.Closure", "Closure.Result.strictProgress"⟩
  ]
  closureMechanisms := [Core.Closure.Mechanism.strictProgress]
  workBound := Node6AvoidingFocus.selectionBudget
  manualObligations := []

/-- Node 8 has no unrecorded mathematical or routing obligation. -/
def node8MetadataComplete :
    Core.Metadata.Complete node8Metadata :=
  ⟨rfl⟩

theorem node8_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node8Metadata.manualObligations) :=
  node8MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused-selection work bound used by the
executor. -/
theorem node8_metadata_work_bounded (previous : Node6AvoidingStage.{u}) :
    node8Metadata.workBound.Within previous
      (node8Metadata.workBound.checks previous) :=
  node8MetadataComplete.work_within previous

#print axioms node8
#print axioms node8Counted_work_bounded
#print axioms node8_noProperCore
#print axioms node8_closure_mechanism
#print axioms node8_metadata_has_no_manual_obligation
#print axioms node8_metadata_work_bounded

end HypostructureErdos64EG
