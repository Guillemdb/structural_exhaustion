import Hypostructure.Graph.RootedReturn
import Hypostructure.Core.Metadata
import HypostructureErdos64EG.Node4

/-!
# Diagram node 5: edge-rooted target algebra

Graph owns the return/cycle dictionary and Core owns focused continuation.
The EG application supplies only the Mersenne instance of the generic shifted
length predicate.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The paper's Mersenne return predicate as a direct graph API instance. -/
def mersenneReturnAlgebra :
    Graph.RootedReturnTargetAlgebra PowerOfTwoLength where
  ReturnLengthOK := MersenneLength
  returnLengthOK_iff_shifted := fun _length => Iff.rfl

/-- The sole payload established by node 5. -/
abbrev Node5Output (stage : Node4Stage.{u})
    (active : Node4Focus.Active stage) :=
  Graph.RootedReturnTargetAlgebra.FocusedAvoidanceCertificateOutput
    Node4Focus mersenneReturnAlgebra node4ContextQuery stage active

/-- Exact accumulated stage after node 5. -/
abbrev Node5Stage :=
  Graph.RootedReturnTargetAlgebra.FocusedAvoidanceCertificateStage
    Node4Focus mersenneReturnAlgebra node4ContextQuery

/-- Counted node-5 execution, including inactive siblings. -/
noncomputable def node5Counted (previous : Node4Stage.{u}) :
    Core.Counted Node5Stage.{u} :=
  Graph.RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted
    Node4Focus mersenneReturnAlgebra node4ContextQuery previous

/-- Graph derives rooted-return avoidance from inherited target avoidance;
Core performs all branch inspection and ledger extension. -/
noncomputable def node5 (previous : Node4Stage.{u}) : Node5Stage.{u} :=
  (node5Counted previous).value

/-- Focus inherited by node 6 and later counterexample nodes. -/
abbrev Node5Focus :=
  Graph.RootedReturnTargetAlgebra.FocusedAvoidanceCertificateProfile
    Node4Focus mersenneReturnAlgebra node4ContextQuery

/-- Typed query for node 5's exact graph-owned certificate. -/
def node5CertificateQuery :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun stage active => Node5Output stage.previous active) :=
  Graph.RootedReturnTargetAlgebra.focusedAvoidanceCertificateQuery
    Node4Focus mersenneReturnAlgebra node4ContextQuery

/-- The minimal context query lifted through node 5 without copying it. -/
def node4ContextAtNode5Query :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun stage active => Node4Output stage.previous.previous active) :=
  node4ContextQuery.preserve

@[simp] theorem node5_previous (previous : Node4Stage.{u}) :
    (node5 previous).previous = previous :=
  rfl

/-- The target/return equivalence remains graph-owned. -/
theorem node5_target_iff_rootedReturn
    (stage : Node4Stage.{u}) (active : Node4Focus.Active stage) :
    Target (node4ContextQuery.read stage active).G <->
      mersenneReturnAlgebra.HasRootedReturn
        (node4ContextQuery.read stage active).G :=
  mersenneReturnAlgebra.target_iff_hasRootedReturn _

@[simp] theorem node5Counted_checks_eq_one (previous : Node4Stage.{u}) :
    (node5Counted previous).checks = 1 := by
  rw [node5Counted,
    Graph.RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted_checks]
  rfl

theorem node5Counted_work_bounded (previous : Node4Stage.{u}) :
    Node4Focus.selectionBudget.Within previous
      (node5Counted previous).checks :=
  Graph.RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted_work_within
    Node4Focus mersenneReturnAlgebra node4ContextQuery previous

/-- Proof-relevant audit record for node-5 rooted-return target algebra. -/
def node5Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node4Stage.{u} Node4Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node5", "node5Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node5", "mersenneReturnAlgebra"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node4", "node4"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node4", "node4ContextQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted"⟩,
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.focusedAvoidanceCertificateQuery"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "Focus.Outcome"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.FocusedAvoidanceCertificateStage"⟩,
      .residualStage⟩,
    ⟨⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.AvoidanceCertificate"⟩,
      .searchResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted_checks"⟩,
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.executeFocusedAvoidanceCertificateCounted_work_within"⟩,
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.target_iff_hasRootedReturn"⟩,
    ⟨"Hypostructure.Graph.RootedReturn",
      "RootedReturnTargetAlgebra.not_target_iff_returnLengthSets_disjoint"⟩
  ]
  workBound := Node4Focus.selectionBudget
  manualObligations := []

/-- Node 5 has no unrecorded mathematical or routing obligation. -/
def node5MetadataComplete :
    Core.Metadata.Complete node5Metadata :=
  ⟨rfl⟩

theorem node5_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node5Metadata.manualObligations) :=
  node5MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same one-check focused-successor budget used by
the counted run. -/
theorem node5_metadata_work_bounded (previous : Node4Stage.{u}) :
    node5Metadata.workBound.Within previous
      (node5Metadata.workBound.checks previous) :=
  node5MetadataComplete.work_within previous

#print axioms node5
#print axioms node5_target_iff_rootedReturn
#print axioms node5Counted_checks_eq_one
#print axioms node5Counted_work_bounded
#print axioms node5_metadata_has_no_manual_obligation
#print axioms node5_metadata_work_bounded

end HypostructureErdos64EG
