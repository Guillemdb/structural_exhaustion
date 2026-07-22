import Hypostructure.Core.Metadata
import Hypostructure.Graph.Obstruction
import HypostructureErdos64EG.Node14

/-!
# Diagram node 15: `P13`-freeness decision

Node 15 runs focused CT1 on the literal node-14 stage.  The public CT1 target
is existence of the induced obstruction `P13`, obtained by instantiating the
graph layer's generic induced-obstruction interface with `pathGraph 13`.  The
C1 terminal therefore feeds the packing branch, while the CT1 avoiding residual
is exactly the paper's `P13`-free branch consumed by the HSS closure node.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- The paper's `P13` obstruction as a local EG parameter. -/
abbrev p13Obstruction :=
  SimpleGraph.pathGraph 13

/-- Node-14's exact proof-projection claim, named here only to keep downstream
universe inference explicit. -/
abbrev Node14Claim :=
  Graph.FocusedNormalizedAtomUncompressibilityClaim.{
    u, 0, v, u + 1}
    Node13Focus.{u, v}
    node4ContextAtNode13Query egNormalizedAtomReplacementProfile
    node11RegistrationAtNode13Query

/-- Node-14's framework-owned proof-projection payload. -/
abbrev Node14Payload (previous : Node13Stage.{u, v})
    (active : Node13Focus.Active previous) :=
  Core.Residual.ProofProjection.Certificate
    Node13Focus.{u, v} Node14Claim.{u, v} previous active

/-- Minimal context lifted through node 14 without copying it into a new
output. -/
def node4ContextAtNode14Query :
    Core.Residual.Focus.ActiveQuery Node14Focus.{u, v}
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode13Query.preserve
    (Output := Node14Payload.{u, v})

/-- Current selected graph, retrieved only from the active node-14 residual. -/
def node15ObjectQuery :
    Core.Residual.Focus.ActiveQuery Node14Focus.{u, v}
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  Graph.focusedMinimalContextObjectQuery Node14Focus.{u, v}
    node4ContextAtNode14Query

/-- The graph-theoretic CT1 target for node 15. -/
def node15Encoding :
    CT1.FocusedCertificateEncoding.Encoding Node14Focus.{u, v}
      (fun previous active =>
        Graph.HasInducedObstruction p13Obstruction
          (node15ObjectQuery.read previous active)) :=
  Graph.CT1.focusedInducedObstructionEncoding Node14Focus.{u, v}
    node15ObjectQuery p13Obstruction

/-- Exact accumulated CT1 decision stage emitted by node 15. -/
abbrev Node15Stage :=
  CT1.FocusedCertificateEncoding.Stage node15Encoding.{u, v}

/-- Counted node-15 execution through Graph's focused induced-obstruction CT1
executor. -/
noncomputable def node15Counted (previous : Node14Stage.{u, v}) :
    Core.Counted Node15Stage.{u, v} :=
  Graph.CT1.executeFocusedInducedObstructionCounted Node14Focus.{u, v}
    node15ObjectQuery p13Obstruction previous

/-- Execute node 15 on the literal node-14 residual. -/
noncomputable def node15 (previous : Node14Stage.{u, v}) :
    Node15Stage.{u, v} :=
  (node15Counted previous).value

/-- Focus inherited after node 15's CT1 extension. -/
abbrev Node15Focus := node15Encoding.{u, v}.SuccessorProfile

@[simp] theorem node15_previous (previous : Node14Stage.{u, v}) :
    (node15 previous).previous = previous :=
  rfl

/-- CT1's terminal has exactly its induced-path / induced-path-free meaning. -/
theorem node15_semantics (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage) :
    match (node15Encoding.{u, v}.routeQuery.read stage active).terminal with
    | .c1 =>
        Graph.HasInducedObstruction p13Obstruction
          (node15ObjectQuery.read stage.previous active)
    | .avoiding =>
        Graph.InducedObstructionFree p13Obstruction
          (node15ObjectQuery.read stage.previous active) := by
  let route := node15Encoding.{u, v}.routeQuery.read stage active
  cases terminal : route.terminal with
  | c1 =>
      exact CT1.FocusedCertificateEncoding.target_of_c1 route terminal
  | avoiding =>
      exact CT1.FocusedCertificateEncoding.avoids_of_avoiding route terminal

/-- Node 15 retains CT1's exact terminal-indexed trace. -/
theorem node15_trace_exact (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage) :
    (CT1.CertificateEncoding.traceOfRoute
      (node15Encoding.{u, v}.routeQuery.read stage active)).nodes =
      CT1.CertificateEncoding.TypedTrace.expectedNodes
        (node15Encoding.{u, v}.routeQuery.read stage active).terminal :=
  (CT1.CertificateEncoding.traceOfRoute
    (node15Encoding.{u, v}.routeQuery.read stage active)).nodes_eq_expected

/-- Focused certificate CT1 performs at most one primitive validation. -/
theorem node15_work_bound (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage) :
    (node15Encoding.{u, v}.routeQuery.read stage active).checks <= 1 := by
  rw [(node15Encoding.{u, v}.routeQuery.read stage active).checks_eq_terminal]
  cases (node15Encoding.{u, v}.routeQuery.read stage active).terminal <;> simp

/-- Total node-15 work includes focus selection and CT1 validation. -/
theorem node15Counted_work_bounded (previous : Node14Stage.{u, v}) :
    node15Encoding.{u, v}.workBudget.Within previous
      (node15Counted previous).checks :=
  node15Encoding.{u, v}.runCounted_work_within previous

/-- Node 15's avoiding arm is exactly the `P13`-free branch. -/
theorem node15_p13_free
    (stage : node15Encoding.{u, v}.AvoidingStage)
    (active : node15Encoding.{u, v}.AvoidingProfile.Active stage) :
    Graph.InducedObstructionFree p13Obstruction
      (node15ObjectQuery.read stage.previous.previous active) :=
  (node15Encoding.{u, v}.avoidingEvidenceQuery.read stage active).avoids

/-- The avoiding branch performs no certificate validation. -/
theorem node15_p13_free_work
    (stage : node15Encoding.{u, v}.AvoidingStage)
    (active : node15Encoding.{u, v}.AvoidingProfile.Active stage) :
    (node15Encoding.{u, v}.routeQuery.read stage.previous active).checks = 0 :=
  (node15Encoding.{u, v}.avoidingEvidenceQuery.read stage active).checks_eq_zero

/-- Proof-relevant audit record for node-15 focused CT1 execution. -/
noncomputable def node15Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node14Stage.{u, v} Node14Stage.{u, v} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node15", "node15Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node15", "node15Encoding"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node14", "node14"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node15",
      "node4ContextAtNode14Query"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node15", "node15ObjectQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node15", "node15ObjectQuery"⟩
    profile := Node14Focus.{u, v}
    Result := fun _stage _active => Graph.FiniteObject.{u}
    query := node15ObjectQuery
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.CT1",
      "executeFocusedInducedObstructionCounted"⟩,
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
  workBound := node15Encoding.{u, v}.workBudget
  manualObligations := []

/-- Node 15 has no unrecorded mathematical or routing obligation. -/
def node15MetadataComplete :
    Core.Metadata.Complete node15Metadata :=
  ⟨rfl⟩

theorem node15_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node15Metadata.manualObligations) :=
  node15MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused CT1 work bound used by the executor. -/
theorem node15_metadata_work_bounded (previous : Node14Stage.{u, v}) :
    node15Metadata.workBound.Within previous
      (node15Metadata.workBound.checks previous) :=
  node15MetadataComplete.work_within previous

#print axioms node15
#print axioms node15_semantics
#print axioms node15_trace_exact
#print axioms node15_work_bound
#print axioms node15Counted_work_bounded
#print axioms node15_p13_free
#print axioms node15_p13_free_work
#print axioms node15_metadata_has_no_manual_obligation
#print axioms node15_metadata_work_bounded

end HypostructureErdos64EG
