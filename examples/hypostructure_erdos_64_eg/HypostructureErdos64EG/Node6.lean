import Hypostructure.Graph.CT1
import Hypostructure.Core.Metadata
import HypostructureErdos64EG.Node5

/-!
# Diagram node 6: exhaustive Mersenne-return decision

Node 6 invokes focused proof-carrying CT1 on node 5's literal stage. CT1 owns
the target decision, certificate validation, routing, trace, and work count.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Current selected graph, retrieved only on the active branch. -/
def node6ObjectQuery :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  Graph.focusedMinimalContextObjectQuery Node5Focus node4ContextAtNode5Query

/-- The entire node-6 specialization: one graph query and the node-5 algebra. -/
def node6Encoding :=
  Graph.CT1.focusedRootedReturnEncoding Node5Focus node6ObjectQuery
    PowerOfTwoLength mersenneReturnAlgebra

/-- Exact accumulated CT1 decision stage emitted by node 6. -/
abbrev Node6Stage :=
  CT1.FocusedCertificateEncoding.Stage node6Encoding

/-- Counted node-6 execution through the public focused graph CT1 executor. -/
noncomputable def node6Counted (previous : Node5Stage.{u}) :
    Core.Counted Node6Stage.{u} :=
  Graph.CT1.executeFocusedRootedReturnCounted Node5Focus node6ObjectQuery
    PowerOfTwoLength mersenneReturnAlgebra previous

/-- Execute node 6 through the public focused graph CT1 executor. -/
noncomputable def node6 (previous : Node5Stage.{u}) : Node6Stage.{u} :=
  (node6Counted previous).value

/-- Focus inherited after node 6's CT1 extension. -/
abbrev Node6Focus := node6Encoding.SuccessorProfile

/-- Typed query for the framework-generated CT1 route. -/
def node6RouteQuery := node6Encoding.routeQuery

/-- Minimal context lifted through node 6 without copying it. -/
def node4ContextAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous active) :=
  node4ContextAtNode5Query.preserve

/-- Node 5's exact return-avoidance certificate retained through node 6. -/
def node5CertificateAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Node5Output stage.previous.previous active) :=
  node5CertificateQuery.preserve

/-- The CT1 object query reindexed to the exact node-6 route stage. -/
def node6ObjectAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  node6ObjectQuery.preserve

/-- The inherited node-5 certificate rules out CT1's public target. -/
def node6TargetImpossibleQuery :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Not (Target (node6ObjectQuery.read stage.previous active))) :=
  mersenneReturnAlgebra.focusedAvoidanceNotTargetQuery Node6Focus
    node6ObjectAtNode6Query node5CertificateAtNode6Query

/-- Framework-owned residual on node 6's exact avoiding arm. -/
abbrev Node6AvoidingStage := node6Encoding.AvoidingStage

/-- Counted closure of the impossible C1 constructor. -/
noncomputable def node6ContinueAvoidingCounted
    (previous : Node6Stage.{u}) : Core.Counted Node6AvoidingStage.{u} :=
  node6Encoding.closeC1ContinueAvoidingCounted
    previous node6TargetImpossibleQuery

/-- Close the impossible C1 constructor and retain node 6's avoiding residual. -/
noncomputable def node6ContinueAvoiding
    (previous : Node6Stage.{u}) : Node6AvoidingStage.{u} :=
  (node6ContinueAvoidingCounted previous).value

/-- Focus inherited by node 8 from node 6's avoiding residual. -/
abbrev Node6AvoidingFocus :=
  node6Encoding.AvoidingProfile

/-- Exact avoiding evidence retained by CT1 on the node-6 edge. -/
def node6AvoidingQuery :
    Core.Residual.Focus.ActiveQuery Node6AvoidingFocus
      (fun stage active =>
        CT1.FocusedCertificateEncoding.AvoidingEvidence
          node6Encoding stage.previous active) :=
  node6Encoding.avoidingEvidenceQuery

@[simp] theorem node6_previous (previous : Node5Stage.{u}) :
    (node6 previous).previous = previous :=
  rfl

/-- CT1's terminal has exactly its local target/avoidance meaning. -/
theorem node6_semantics (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    match (node6RouteQuery.read stage active).terminal with
    | .c1 => Target (node6ObjectQuery.read stage.previous active)
    | .avoiding => Not (Target (node6ObjectQuery.read stage.previous active)) := by
  let route := node6RouteQuery.read stage active
  cases terminal : route.terminal with
  | c1 =>
      exact CT1.FocusedCertificateEncoding.target_of_c1 route terminal
  | avoiding =>
      exact CT1.FocusedCertificateEncoding.avoids_of_avoiding route terminal

/-- Node 6 retains CT1's exact terminal-indexed trace. -/
theorem node6_trace_exact (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    (CT1.CertificateEncoding.traceOfRoute
      (node6RouteQuery.read stage active)).nodes =
      CT1.CertificateEncoding.TypedTrace.expectedNodes
        (node6RouteQuery.read stage active).terminal :=
  (CT1.CertificateEncoding.traceOfRoute
    (node6RouteQuery.read stage active)).nodes_eq_expected

/-- Focused certificate CT1 performs at most one primitive validation. -/
theorem node6_work_bound (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    (node6RouteQuery.read stage active).checks <= 1 := by
  rw [(node6RouteQuery.read stage active).checks_eq_terminal]
  cases (node6RouteQuery.read stage active).terminal <;> simp

/-- Total node-6 work includes focus selection and CT1 validation. -/
theorem node6Counted_work_bounded (previous : Node5Stage.{u}) :
    node6Encoding.workBudget.Within previous
      (node6Counted previous).checks :=
  node6Encoding.runCounted_work_within previous

/-- The avoidance continuation also accounts for its focus selection. -/
theorem node6ContinueAvoidingCounted_work_bounded
    (previous : Node6Stage.{u}) :
    node6Encoding.SuccessorProfile.selectionBudget.Within previous
      (node6ContinueAvoidingCounted previous).checks :=
  node6Encoding.closeC1ContinueAvoidingCounted_work_within
    previous node6TargetImpossibleQuery

@[simp] theorem node6ContinueAvoiding_previous (previous : Node6Stage.{u}) :
    (node6ContinueAvoiding previous).previous = previous :=
  rfl

/-- Node 6's continuation arm exactly avoids the public target. -/
theorem node6_avoids (stage : Node6AvoidingStage.{u})
    (active : Node6AvoidingFocus.Active stage) :
    Not (Target (node6ObjectQuery.read stage.previous.previous active)) :=
  (node6AvoidingQuery.read stage active).avoids

/-- The avoiding arm performs no certificate validation. -/
theorem node6_avoiding_work (stage : Node6AvoidingStage.{u})
    (active : Node6AvoidingFocus.Active stage) :
    (node6RouteQuery.read stage.previous active).checks = 0 :=
  (node6AvoidingQuery.read stage active).checks_eq_zero

/-- Proof-relevant audit record for node-6 focused CT1 execution. -/
noncomputable def node6Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node5Stage.{u} Node5Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node6", "node6Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node6", "node6Encoding"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node5", "node5"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node6", "node6ObjectQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node6", "node6ObjectQuery"⟩
    profile := Node5Focus
    Result := fun _stage _active => Graph.FiniteObject.{u}
    query := node6ObjectQuery
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.CT1",
      "executeFocusedRootedReturnCounted"⟩,
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.runCounted"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.Route"⟩, .typedOutcome⟩,
    ⟨⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.Stage"⟩, .residualStage⟩,
    ⟨⟨"Hypostructure.CT1.CertificateEncoding",
      "traceOfRoute"⟩, .executionTrace⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.target_of_c1"⟩,
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.avoids_of_avoiding"⟩,
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.runCounted_work_within"⟩
  ]
  workBound := node6Encoding.workBudget
  manualObligations := []

/-- Proof-relevant audit record for node-6's impossible-C1 continuation. -/
noncomputable def node6ContinueAvoidingMetadata :
    Core.Metadata.DeclarationMetadata.{u + 1, 0, u + 1}
      Node6Stage.{u} Node6Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node6",
      "node6ContinueAvoidingCounted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node6",
      "node6TargetImpossibleQuery"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node6", "node6"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node5",
      "node5CertificateQuery"⟩, .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.closeC1ContinueAvoidingCounted"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.AvoidingEvidence"⟩, .searchResult⟩,
    ⟨⟨"Hypostructure.Core.Residual.Focus", "runCounted"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.closeC1ContinueAvoidingCounted_work_within"⟩,
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.closeC1ContinueAvoiding_previous"⟩
  ]
  workBound := node6Encoding.SuccessorProfile.selectionBudget
  manualObligations := []

/-- Node 6 CT1 execution has no unrecorded mathematical or routing obligation. -/
def node6MetadataComplete :
    Core.Metadata.Complete node6Metadata :=
  ⟨rfl⟩

/-- Node 6's avoiding continuation has no unrecorded mathematical or routing
obligation. -/
def node6ContinueAvoidingMetadataComplete :
    Core.Metadata.Complete node6ContinueAvoidingMetadata :=
  ⟨rfl⟩

theorem node6_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node6Metadata.manualObligations) :=
  node6MetadataComplete.no_manual_obligation obligation

theorem node6_continue_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node6ContinueAvoidingMetadata.manualObligations) :=
  node6ContinueAvoidingMetadataComplete.no_manual_obligation obligation

theorem node6_metadata_work_bounded (previous : Node5Stage.{u}) :
    node6Metadata.workBound.Within previous
      (node6Metadata.workBound.checks previous) :=
  node6MetadataComplete.work_within previous

theorem node6_continue_metadata_work_bounded
    (previous : Node6Stage.{u}) :
    node6ContinueAvoidingMetadata.workBound.Within previous
      (node6ContinueAvoidingMetadata.workBound.checks previous) :=
  node6ContinueAvoidingMetadataComplete.work_within previous

#print axioms node6
#print axioms node6Counted_work_bounded
#print axioms node6ContinueAvoiding
#print axioms node6ContinueAvoidingCounted_work_bounded
#print axioms node6_semantics
#print axioms node6_trace_exact
#print axioms node6_work_bound
#print axioms node6_avoids
#print axioms node6_avoiding_work
#print axioms node6_metadata_has_no_manual_obligation
#print axioms node6_continue_metadata_has_no_manual_obligation
#print axioms node6_metadata_work_bounded
#print axioms node6_continue_metadata_work_bounded

end HypostructureErdos64EG
