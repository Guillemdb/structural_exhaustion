import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Decision
import HypostructureErdos64EG.Contract
import HypostructureErdos64EG.Node1

/-!
# Diagram node 2: exhaustive counterexample decision

The minimum-degree premise is already in the root residual.  Node 2 asks the
paper's exact question and lets Core construct both dependent branches.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Framework query for the unique residual carried by node 1. -/
def node1ResidualQuery :
    Core.Residual.Query Node1Stage (fun _stage => InitialResidual.{u}) :=
  Core.Residual.Query.residual

/-- The exact positive branch of diagram node 2. -/
def IsCounterexample (stage : Node1Stage.{u}) : Prop :=
  EGCounterexample (node1ResidualQuery.read stage)

/-- The exact negative branch of diagram node 2. -/
def IsNotCounterexample (stage : Node1Stage.{u}) : Prop :=
  EGNotCounterexample (node1ResidualQuery.read stage)

/-- Core-owned exhaustive decision profile for node 2. -/
noncomputable def node2Decision :
    Core.Residual.Decision.Node Node1Stage IsCounterexample
      IsNotCounterexample :=
  Core.Residual.Decision.Node.create
    (fun stage => by
      classical
      exact inferInstanceAs (Decidable (IsCounterexample stage)))
    (fun stage absent => by
      let residual := node1ResidualQuery.read stage
      change Target residual.object
      by_contra avoids
      exact absent ⟨residual.baseline, avoids⟩)

/-- Exact accumulated stage emitted by diagram node 2. -/
abbrev Node2Stage :=
  Core.Residual.Decision.Stage IsCounterexample IsNotCounterexample

/-- Node 2 performs one framework-owned binary branch inspection. -/
noncomputable abbrev node2WorkBudget :
    Core.PolynomialCheckBudget Node1Stage.{u} :=
  node2Decision.workBudget

/-- Counted execution of the exact Core decision on its node-1 predecessor. -/
noncomputable def node2Counted (previous : Node1Stage.{u}) :
    Core.Counted Node2Stage.{u} :=
  node2Decision.runCounted previous

/-- Execute node 2 on its literal node-1 predecessor. -/
noncomputable def node2 (previous : Node1Stage.{u}) : Node2Stage.{u} :=
  (node2Counted previous).value

@[simp] theorem node2Counted_value (previous : Node1Stage.{u}) :
    (node2Counted previous).value = node2 previous :=
  rfl

@[simp] theorem node2_previous (previous : Node1Stage.{u}) :
    (node2 previous).previous = previous :=
  rfl

/-- Node 2 exposes exactly the two branches in the manuscript. -/
theorem node2_exhaustive (previous : Node1Stage.{u}) :
    match (node2 previous).added with
    | .yesBranch _proof => IsCounterexample previous
    | .noBranch _proof => IsNotCounterexample previous := by
  cases (node2 previous).added with
  | yesBranch proof => exact proof
  | noBranch proof => exact proof

/-- A target certificate forces the exact negative constructor. -/
theorem node2_no_branch_of_target (previous : Node1Stage.{u})
    (target : IsNotCounterexample previous) :
    ∃ proof : IsNotCounterexample previous,
      (node2 previous).added =
        Core.Residual.Decision.Binary.noBranch proof := by
  exact node2Decision.runCounted_added_no_of_not_yes
    (previous := previous) fun counterexample => counterexample.2 target

/-- A counterexample certificate forces the exact positive constructor. -/
theorem node2_yes_branch_of_counterexample (previous : Node1Stage.{u})
    (counterexample : IsCounterexample previous) :
    ∃ proof : IsCounterexample previous,
      (node2 previous).added =
        Core.Residual.Decision.Binary.yesBranch proof := by
  exact node2Decision.runCounted_added_yes_of_yes
    (previous := previous) counterexample

@[simp] theorem node2Counted_checks_eq_one (previous : Node1Stage.{u}) :
    (node2Counted previous).checks = 1 :=
  rfl

@[simp] theorem node2Counted_checks_eq_budget (previous : Node1Stage.{u}) :
    (node2Counted previous).checks = node2WorkBudget.checks previous :=
  Core.Residual.Decision.Node.runCounted_checks node2Decision previous

/-- The Core binary decision satisfies its constant one-check work budget. -/
theorem node2_work_bounded (previous : Node1Stage.{u}) :
    node2WorkBudget.Within previous (node2Counted previous).checks :=
  node2Decision.runCounted_work_within previous

/-- Proof-relevant audit record for the node-2 counterexample decision. -/
noncomputable def node2Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node1Stage.{u} Node1Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node2", "node2Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node2", "node2Decision.yesDecidable"⟩,
      .decisionProcedure⟩,
    ⟨⟨"HypostructureErdos64EG.Node2", "node2Decision.no_of_not_yes"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node1", "node1ResidualQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node1", "node1ResidualQuery"⟩
    Result := fun _stage => InitialResidual.{u}
    query := node1ResidualQuery
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Core.Residual.Decision", "Decision.Node.runCounted"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Decision", "Decision.Binary"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Core.Residual.Decision", "Decision.Stage"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Residual.Decision", "Decision.Node.run_previous"⟩,
    ⟨"Hypostructure.Core.Residual.Decision",
      "Decision.Node.runCounted_work_within"⟩,
    ⟨"Hypostructure.Core.Residual.Decision",
      "Decision.Node.runCounted_added_yes_of_yes"⟩,
    ⟨"Hypostructure.Core.Residual.Decision",
      "Decision.Node.runCounted_added_no_of_not_yes"⟩
  ]
  workBound := node2WorkBudget
  manualObligations := []

/-- Node 2 has no unrecorded mathematical or routing obligation. -/
def node2MetadataComplete :
    Core.Metadata.Complete node2Metadata :=
  ⟨rfl⟩

theorem node2_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node2Metadata.manualObligations) :=
  node2MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same one-check budget used by the counted run. -/
theorem node2_metadata_work_bounded (previous : Node1Stage.{u}) :
    node2Metadata.workBound.Within previous
      (node2Metadata.workBound.checks previous) :=
  node2MetadataComplete.work_within previous

#print axioms node2
#print axioms node2_exhaustive
#print axioms node2_yes_branch_of_counterexample
#print axioms node2_no_branch_of_target
#print axioms node2Counted_checks_eq_one
#print axioms node2Counted_checks_eq_budget
#print axioms node2_work_bounded
#print axioms node2_metadata_has_no_manual_obligation
#print axioms node2_metadata_work_bounded

end HypostructureErdos64EG
